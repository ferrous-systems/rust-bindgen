//! A higher level Clang API built on top of the generated bindings in the
//! `clang_sys` module.

#![allow(non_upper_case_globals, dead_code)]
#![deny(clippy::missing_docs_in_private_items)]

use crate::ir::context::BindgenContext;
use clang::token::TokenKind;
use clang::{Entity, EntityKind, EntityVisitResult};
use std::ffi::{CStr, CString};
use std::fmt;
use std::hash::Hash;
use std::hash::Hasher;
use std::os::raw::{c_char, c_int, c_longlong, c_uint, c_ulong, c_ulonglong};
use std::{mem, ptr, slice};

/// Type representing a clang attribute.
///
/// Values of this type can be used to check for different attributes using the `has_attrs`
/// function.
pub(crate) struct Attribute {
    name: &'static [u8],
    kind: Option<EntityKind>,
    token_kind: TokenKind,
}

impl Attribute {
    /// A `warn_unused_result` attribute.
    pub(crate) const MUST_USE: Self = Self {
        name: b"warn_unused_result",
        // FIXME(emilio): clang-sys doesn't expose `EntityKind::WarnUnusedResultAttr` (from clang 9).
        kind: Some(EntityKind::WarnUnusedResultAttr),
        token_kind: TokenKind::Identifier,
    };

    /// A `_Noreturn` attribute.
    pub(crate) const NO_RETURN: Self = Self {
        name: b"_Noreturn",
        kind: None,
        token_kind: TokenKind::Keyword,
    };

    /// A `[[noreturn]]` attribute.
    pub(crate) const NO_RETURN_CPP: Self = Self {
        name: b"noreturn",
        kind: None,
        token_kind: TokenKind::Identifier,
    };
}

/// A cursor into the Clang AST, pointing to an AST node.
///
/// We call the AST node pointed to by the cursor the cursor's "referent".
#[derive(Copy, Clone)]
pub(crate) struct Cursor<'tu> {
    entity: Option<Entity<'tu>>,
}

impl<'tu> fmt::Debug for Cursor<'tu> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(
            fmt,
            "Cursor({} kind: {}, loc: {}, usr: {:?})",
            self.spelling(),
            kind_to_str(self.kind()),
            self.location(),
            self.usr()
        )
    }
}

impl<'tu> Cursor<'tu> {
    /// Get the Unified Symbol Resolution for this cursor's referent, if
    /// available.
    ///
    /// The USR can be used to compare entities across translation units.
    pub(crate) fn usr(&self) -> Option<String> {
        Some(self.entity.as_ref()?.get_usr()?.0)
    }

    /// Is this cursor's referent a declaration?
    pub(crate) fn is_declaration(&self) -> bool {
        self.entity.map(|e| e.is_declaration()).unwrap_or_default()
    }

    /// Is this cursor's referent an anonymous record or so?
    pub(crate) fn is_anonymous(&self) -> bool {
        self.entity.map(|e| e.is_anonymous()).unwrap_or_default()
    }

    /// Get this cursor's referent's spelling.
    pub(crate) fn spelling(&self) -> String {
        self.entity.and_then(|e| e.get_name()).unwrap_or_default()
    }

    /// Get this cursor's referent's display name.
    ///
    /// This is not necessarily a valid identifier. It includes extra
    /// information, such as parameters for a function, etc.
    pub(crate) fn display_name(&self) -> String {
        self.entity
            .and_then(|e| e.get_display_name())
            .unwrap_or_default()
    }

    /// Get the mangled name of this cursor's referent.
    pub(crate) fn mangling(&self) -> String {
        self.entity
            .and_then(|e| e.get_mangled_name())
            .unwrap_or_default()
    }

    /// Gets the C++ manglings for this cursor, or an error if the manglings
    /// are not available.
    pub(crate) fn cxx_manglings(&self) -> Result<Vec<String>, ()> {
        self.entity.and_then(|e| e.get_mangled_names()).ok_or(())
    }

    /// Returns whether the cursor refers to a built-in definition.
    pub(crate) fn is_builtin(&self) -> bool {
        self.entity
            .and_then(|e| {
                Some(e.get_location()?.get_file_location().file.is_none())
            })
            .unwrap_or_default()
    }

    /// Get the `Cursor` for this cursor's referent's lexical parent.
    ///
    /// The lexical parent is the parent of the definition. The semantic parent
    /// is the parent of the declaration. Generally, the lexical parent doesn't
    /// have any effect on semantics, while the semantic parent does.
    ///
    /// In the following snippet, the `Foo` class would be the semantic parent
    /// of the out-of-line `method` definition, while the lexical parent is the
    /// translation unit.
    ///
    /// ```c++
    /// class Foo {
    ///     void method();
    /// };
    ///
    /// void Foo::method() { /* ... */ }
    /// ```
    pub(crate) fn lexical_parent(&self) -> Cursor {
        Cursor {
            entity: self.entity.and_then(|e| e.get_lexical_parent()),
        }
    }

    /// Get the referent's semantic parent, if one is available.
    ///
    /// See documentation for `lexical_parent` for details on semantic vs
    /// lexical parents.
    pub(crate) fn fallible_semantic_parent(&self) -> Option<Cursor> {
        match self.entity {
            Some(ref e) => Some(Cursor {
                entity: Some(e.get_semantic_parent()?),
            }),
            None => Some(Cursor { entity: None }),
        }
    }

    /// Get the referent's semantic parent.
    ///
    /// See documentation for `lexical_parent` for details on semantic vs
    /// lexical parents.
    pub(crate) fn semantic_parent(&self) -> Cursor {
        self.fallible_semantic_parent().unwrap()
    }

    /// Return the number of template arguments used by this cursor's referent,
    /// if the referent is either a template instantiation. Returns `None`
    /// otherwise.
    ///
    /// NOTE: This may not return `Some` for partial template specializations,
    /// see #193 and #194.
    pub(crate) fn num_template_args(&self) -> Option<usize> {
        // XXX: `clang_Type_getNumTemplateArguments` is sort of reliable, while
        // `clang_Cursor_getNumTemplateArguments` is totally unreliable.
        // Therefore, try former first, and only fallback to the latter if we
        // have to.

        self.cur_type()
            .num_template_args()
            .or_else(|| Some(self.entity?.get_template_arguments()?.len()))
            .or_else(|| {
                let canonical = self.canonical();
                if canonical != *self {
                    canonical.num_template_args()
                } else {
                    None
                }
            })
    }

    /// Get a cursor pointing to this referent's containing translation unit.
    ///
    /// Note that we shouldn't create a `TranslationUnit` struct here, because
    /// bindgen assumes there will only be one of them alive at a time, and
    /// disposes it on drop. That can change if this would be required, but I
    /// think we can survive fine without it.
    pub(crate) fn translation_unit(&self) -> Cursor {
        assert!(self.is_valid());
        let cursor = Cursor {
            entity: Some(
                self.entity.unwrap().get_translation_unit().get_entity(),
            ),
        };
        assert!(cursor.is_valid());
        cursor
    }

    /// Is the referent a top level construct?
    pub(crate) fn is_toplevel(&self) -> bool {
        let mut semantic_parent = self.fallible_semantic_parent();

        while semantic_parent.is_some() &&
            (semantic_parent.unwrap().kind() == EntityKind::Namespace ||
                semantic_parent.unwrap().kind() ==
                    EntityKind::NamespaceAlias ||
                semantic_parent.unwrap().kind() ==
                    EntityKind::NamespaceRef)
        {
            semantic_parent =
                semantic_parent.unwrap().fallible_semantic_parent();
        }

        let tu = self.translation_unit();
        // Yes, this can happen with, e.g., macro definitions.
        semantic_parent == tu.fallible_semantic_parent()
    }

    /// There are a few kinds of types that we need to treat specially, mainly
    /// not tracking the type declaration but the location of the cursor, given
    /// clang doesn't expose a proper declaration for these types.
    pub(crate) fn is_template_like(&self) -> bool {
        matches!(
            self.kind(),
            Some(EntityKind::ClassTemplate) |
                Some(EntityKind::ClassTemplatePartialSpecialization) |
                Some(EntityKind::TypeAliasTemplateDecl)
        )
    }

    /// Is this Cursor pointing to a function-like macro definition?
    pub(crate) fn is_macro_function_like(&self) -> bool {
        self.entity
            .map(|e| e.is_function_like_macro())
            .unwrap_or_default()
    }

    /// Get the kind of referent this cursor is pointing to.
    pub(crate) fn kind(&self) -> Option<EntityKind> {
        self.entity.map(|e| e.get_kind())
    }

    /// Returns true if the cursor is a definition
    pub(crate) fn is_definition(&self) -> bool {
        self.entity.map(|e| e.is_definition()).unwrap_or_default()
    }

    /// Is the referent a template specialization?
    pub(crate) fn is_template_specialization(&self) -> bool {
        self.specialized().is_some()
    }

    /// Is the referent a fully specialized template specialization without any
    /// remaining free template arguments?
    pub(crate) fn is_fully_specialized_template(&self) -> bool {
        self.is_template_specialization() &&
            self.kind() !=
                Some(EntityKind::ClassTemplatePartialSpecialization)
    }

    /// Is the referent a template specialization that still has remaining free
    /// template arguments?
    pub(crate) fn is_in_non_fully_specialized_template(&self) -> bool {
        if self.is_toplevel() {
            return false;
        }

        let parent = self.semantic_parent();
        if parent.is_fully_specialized_template() {
            return false;
        }

        if !parent.is_template_like() {
            return parent.is_in_non_fully_specialized_template();
        }

        true
    }

    /// Is the referent any kind of template parameter?
    pub(crate) fn is_template_parameter(&self) -> bool {
        matches!(
            self.kind(),
            Some(EntityKind::TemplateTemplateParameter) |
                Some(EntityKind::TemplateTypeParameter) |
                Some(EntityKind::NonTypeTemplateParameter)
        )
    }

    /// Does the referent's type or value depend on a template parameter?
    pub(crate) fn is_dependent_on_template_parameter(&self) -> bool {
        fn visitor(
            found_template_parameter: &mut bool,
            cur: Cursor,
        ) -> EntityVisitResult {
            // If we found a template parameter, it is dependent.
            if cur.is_template_parameter() {
                *found_template_parameter = true;
                return EntityVisitResult::Break;
            }

            // Get the referent and traverse it as well.
            if let Some(referenced) = cur.referenced() {
                if referenced.is_template_parameter() {
                    *found_template_parameter = true;
                    return EntityVisitResult::Break;
                }

                referenced
                    .visit(|next| visitor(found_template_parameter, next));
                if *found_template_parameter {
                    return EntityVisitResult::Break;
                }
            }

            // Continue traversing the AST at the original cursor.
            EntityVisitResult::Recurse
        }

        if self.is_template_parameter() {
            return true;
        }

        let mut found_template_parameter = false;
        self.visit(|next| visitor(&mut found_template_parameter, next));

        found_template_parameter
    }

    /// Is this cursor pointing a valid referent?
    pub(crate) fn is_valid(&self) -> bool {
        self.kind().map(|e| e.is_valid()).unwrap_or_default()
    }

    /// Get the source location for the referent.
    pub(crate) fn location(&self) -> SourceLocation {
        SourceLocation {
            location: self.entity.and_then(|e| e.get_location()),
        }
    }

    /// Get the source location range for the referent.
    pub(crate) fn extent(&self) -> SourceRange {
        SourceRange {
            range: self.entity.map(|e| e.get_range()),
        }
    }

    /// Get the raw declaration comment for this referent, if one exists.
    pub(crate) fn raw_comment(&self) -> Option<String> {
        self.entity?.get_comment()
    }

    /// Get the referent's parsed comment.
    pub(crate) fn comment(&self) -> Comment {
        unsafe {
            Comment {
                comment: self.entity.map(|e| e.get_parsed_comment()),
            }
        }
    }

    /// Get the referent's type.
    pub(crate) fn cur_type(&self) -> Type {
        unsafe {
            Type {
                ty: self.entity.and_then(|e| e.get_type()),
            }
        }
    }

    /// Given that this cursor's referent is a reference to another type, or is
    /// a declaration, get the cursor pointing to the referenced type or type of
    /// the declared thing.
    pub(crate) fn definition(&self) -> Option<Cursor> {
        let ret = Cursor {
            entity: self.entity.and_then(|e| e.get_definition()),
        };

        if ret.is_valid() && ret.kind() != Some(EntityKind::InvalidDecl) {
            Some(ret)
        } else {
            None
        }
    }

    /// Given that this cursor's referent is reference type, get the cursor
    /// pointing to the referenced type.
    pub(crate) fn referenced(&self) -> Option<Cursor> {
        unsafe {
            let ret = Cursor {
                entity: self.entity.and_then(|e| e.get_reference()),
            };

            if ret.is_valid() {
                Some(ret)
            } else {
                None
            }
        }
    }

    /// Get the canonical cursor for this referent.
    ///
    /// Many types can be declared multiple times before finally being properly
    /// defined. This method allows us to get the canonical cursor for the
    /// referent type.
    pub(crate) fn canonical(&self) -> Cursor {
        unsafe {
            Cursor {
                entity: self.entity.map(|e| e.get_canonical_entity()),
            }
        }
    }

    /// Given that this cursor points to either a template specialization or a
    /// template instantiation, get a cursor pointing to the template definition
    /// that is being specialized.
    pub(crate) fn specialized(&self) -> Option<Cursor> {
        unsafe {
            let ret = Cursor {
                entity: self.entity.and_then(|e| e.get_template()),
            };
            if ret.is_valid() {
                Some(ret)
            } else {
                None
            }
        }
    }

    /// Assuming that this cursor's referent is a template declaration, get the
    /// kind of cursor that would be generated for its specializations.
    pub(crate) fn template_kind(&self) -> Option<EntityKind> {
        self.entity.and_then(|e| e.get_template_kind())
    }

    /// Traverse this cursor's referent and its children.
    ///
    /// Call the given function on each AST node traversed.
    pub(crate) fn visit<Visitor>(&self, mut visitor: Visitor)
    where
        Visitor: FnMut(Cursor<'tu>) -> EntityVisitResult,
    {
        if let Some(ref e) = self.entity {
            e.visit_children(|entity, _parent| {
                visitor(Cursor {
                    entity: Some(entity),
                })
            });
        }
    }

    /// Collect all of this cursor's children into a vec and return them.
    pub(crate) fn collect_children(&self) -> Vec<Cursor<'tu>> {
        let mut children = vec![];
        self.visit(|c| {
            children.push(c);
            EntityVisitResult::Continue
        });
        children
    }

    /// Does this cursor have any children?
    pub(crate) fn has_children(&self) -> bool {
        let mut has_children = false;
        self.visit(|_| {
            has_children = true;
            EntityVisitResult::Break
        });
        has_children
    }

    /// Does this cursor have at least `n` children?
    pub(crate) fn has_at_least_num_children(&self, n: usize) -> bool {
        assert!(n > 0);
        let mut num_left = n;
        self.visit(|_| {
            num_left -= 1;
            if num_left == 0 {
                EntityVisitResult::Break
            } else {
                EntityVisitResult::Continue
            }
        });
        num_left == 0
    }

    /// Returns whether the given location contains a cursor with the given
    /// kind in the first level of nesting underneath (doesn't look
    /// recursively).
    pub(crate) fn contains_cursor(&self, kind: CXCursorKind) -> bool {
        let mut found = false;

        self.visit(|c| {
            if c.kind() == kind {
                found = true;
                EntityVisitResult::Break
            } else {
                EntityVisitResult::Continue
            }
        });

        found
    }

    /// Is the referent an inlined function?
    pub(crate) fn is_inlined_function(&self) -> bool {
        unsafe { clang_Cursor_isFunctionInlined(self.entity) != 0 }
    }

    /// Is the referent a defaulted function?
    pub(crate) fn is_defaulted_function(&self) -> bool {
        unsafe { clang_CXXMethod_isDefaulted(self.entity) != 0 }
    }

    /// Is the referent a deleted function?
    pub(crate) fn is_deleted_function(&self) -> bool {
        // Unfortunately, libclang doesn't yet have an API for checking if a
        // member function is deleted, but the following should be a good
        // enough approximation.
        // Deleted functions are implicitly inline according to paragraph 4 of
        // [dcl.fct.def.delete] in the C++ standard. Normal inline functions
        // have a definition in the same translation unit, so if this is an
        // inline function without a definition, and it's not a defaulted
        // function, we can reasonably safely conclude that it's a deleted
        // function.
        self.is_inlined_function() &&
            self.definition().is_none() &&
            !self.is_defaulted_function()
    }

    /// Is the referent a bit field declaration?
    pub(crate) fn is_bit_field(&self) -> bool {
        unsafe { clang_Cursor_isBitField(self.entity) != 0 }
    }

    /// Get a cursor to the bit field's width expression, or `None` if it's not
    /// a bit field.
    pub(crate) fn bit_width_expr(&self) -> Option<Cursor> {
        if !self.is_bit_field() {
            return None;
        }

        let mut result = None;
        self.visit(|cur| {
            // The first child may or may not be a TypeRef, depending on whether
            // the field's type is builtin. Skip it.
            if cur.kind() == EntityKind::TypeRef {
                return EntityVisitResult::Continue;
            }

            // The next expression or literal is the bit width.
            result = Some(cur);

            EntityVisitResult::Break
        });

        result
    }

    /// Get the width of this cursor's referent bit field, or `None` if the
    /// referent is not a bit field or if the width could not be evaluated.
    pub(crate) fn bit_width(&self) -> Option<u32> {
        // It is not safe to check the bit width without ensuring it doesn't
        // depend on a template parameter. See
        // https://github.com/rust-lang/rust-bindgen/issues/2239
        if self.bit_width_expr()?.is_dependent_on_template_parameter() {
            return None;
        }

        unsafe {
            let w = clang_getFieldDeclBitWidth(self.entity);
            if w == -1 {
                None
            } else {
                Some(w as u32)
            }
        }
    }

    /// Get the integer representation type used to hold this cursor's referent
    /// enum type.
    pub(crate) fn enum_type(&self) -> Option<Type> {
        unsafe {
            let t = Type {
                ty: clang_getEnumDeclIntegerType(self.entity),
            };
            if t.is_valid() {
                Some(t)
            } else {
                None
            }
        }
    }

    /// Get the boolean constant value for this cursor's enum variant referent.
    ///
    /// Returns None if the cursor's referent is not an enum variant.
    pub(crate) fn enum_val_boolean(&self) -> Option<bool> {
        unsafe {
            if self.kind() == EntityKind::EnumConstantDecl {
                Some(clang_getEnumConstantDeclValue(self.entity) != 0)
            } else {
                None
            }
        }
    }

    /// Get the signed constant value for this cursor's enum variant referent.
    ///
    /// Returns None if the cursor's referent is not an enum variant.
    pub(crate) fn enum_val_signed(&self) -> Option<i64> {
        unsafe {
            if self.kind() == EntityKind::EnumConstantDecl {
                #[allow(clippy::unnecessary_cast)]
                Some(clang_getEnumConstantDeclValue(self.entity) as i64)
            } else {
                None
            }
        }
    }

    /// Get the unsigned constant value for this cursor's enum variant referent.
    ///
    /// Returns None if the cursor's referent is not an enum variant.
    pub(crate) fn enum_val_unsigned(&self) -> Option<u64> {
        unsafe {
            if self.kind() == EntityKind::EnumConstantDecl {
                #[allow(clippy::unnecessary_cast)]
                Some(clang_getEnumConstantDeclUnsignedValue(self.entity) as u64)
            } else {
                None
            }
        }
    }

    /// Does this cursor have the given attributes?
    pub(crate) fn has_attrs<const N: usize>(
        &self,
        attrs: &[Attribute; N],
    ) -> [bool; N] {
        let mut found_attrs = [false; N];
        let mut found_count = 0;

        self.visit(|cur| {
            let kind = cur.kind();
            for (idx, attr) in attrs.iter().enumerate() {
                let found_attr = &mut found_attrs[idx];
                if !*found_attr {
                    // `attr.name` and` attr.token_kind` are checked against unexposed attributes only.
                    if attr.kind.map_or(false, |k| k == kind) ||
                        (kind == EntityKind::UnexposedAttr &&
                            cur.tokens().iter().any(|t| {
                                t.kind == attr.token_kind &&
                                    t.spelling() == attr.name
                            }))
                    {
                        *found_attr = true;
                        found_count += 1;

                        if found_count == N {
                            return EntityVisitResult::Break;
                        }
                    }
                }
            }

            EntityVisitResult::Continue
        });

        found_attrs
    }

    /// Given that this cursor's referent is a `typedef`, get the `Type` that is
    /// being aliased.
    pub(crate) fn typedef_type(&self) -> Option<Type> {
        let inner = Type {
            ty: unsafe { clang_getTypedefDeclUnderlyingType(self.entity) },
        };

        if inner.is_valid() {
            Some(inner)
        } else {
            None
        }
    }

    /// Get the linkage kind for this cursor's referent.
    ///
    /// This only applies to functions and variables.
    pub(crate) fn linkage(&self) -> CXLinkageKind {
        unsafe { clang_getCursorLinkage(self.entity) }
    }

    /// Get the visibility of this cursor's referent.
    pub(crate) fn visibility(&self) -> CXVisibilityKind {
        unsafe { clang_getCursorVisibility(self.entity) }
    }

    /// Given that this cursor's referent is a function, return cursors to its
    /// parameters.
    ///
    /// Returns None if the cursor's referent is not a function/method call or
    /// declaration.
    pub(crate) fn args(&self) -> Option<Vec<Cursor>> {
        // match self.kind() {
        // EntityKind::FunctionDecl |
        // EntityKind::CXXMethod => {
        self.num_args().ok().map(|num| {
            (0..num)
                .map(|i| Cursor {
                    entity: unsafe {
                        clang_Cursor_getArgument(self.entity, i as c_uint)
                    },
                })
                .collect()
        })
    }

    /// Given that this cursor's referent is a function/method call or
    /// declaration, return the number of arguments it takes.
    ///
    /// Returns Err if the cursor's referent is not a function/method call or
    /// declaration.
    pub(crate) fn num_args(&self) -> Result<u32, ()> {
        unsafe {
            let w = clang_Cursor_getNumArguments(self.entity);
            if w == -1 {
                Err(())
            } else {
                Ok(w as u32)
            }
        }
    }

    /// Get the access specifier for this cursor's referent.
    pub(crate) fn access_specifier(&self) -> CX_CXXAccessSpecifier {
        unsafe { clang_getCXXAccessSpecifier(self.entity) }
    }

    /// Is the cursor's referrent publically accessible in C++?
    ///
    /// Returns true if self.access_specifier() is `CX_CXXPublic` or
    /// `CX_CXXInvalidAccessSpecifier`.
    pub(crate) fn public_accessible(&self) -> bool {
        let access = self.access_specifier();
        access == CX_CXXPublic || access == CX_CXXInvalidAccessSpecifier
    }

    /// Is this cursor's referent a field declaration that is marked as
    /// `mutable`?
    pub(crate) fn is_mutable_field(&self) -> bool {
        unsafe { clang_CXXField_isMutable(self.entity) != 0 }
    }

    /// Get the offset of the field represented by the Cursor.
    pub(crate) fn offset_of_field(&self) -> Result<usize, LayoutError> {
        let offset = unsafe { clang_Cursor_getOffsetOfField(self.entity) };

        if offset < 0 {
            Err(LayoutError::from(offset as i32))
        } else {
            Ok(offset as usize)
        }
    }

    /// Is this cursor's referent a member function that is declared `static`?
    pub(crate) fn method_is_static(&self) -> bool {
        unsafe { clang_CXXMethod_isStatic(self.entity) != 0 }
    }

    /// Is this cursor's referent a member function that is declared `const`?
    pub(crate) fn method_is_const(&self) -> bool {
        unsafe { clang_CXXMethod_isConst(self.entity) != 0 }
    }

    /// Is this cursor's referent a member function that is virtual?
    pub(crate) fn method_is_virtual(&self) -> bool {
        unsafe { clang_CXXMethod_isVirtual(self.entity) != 0 }
    }

    /// Is this cursor's referent a member function that is pure virtual?
    pub(crate) fn method_is_pure_virtual(&self) -> bool {
        unsafe { clang_CXXMethod_isPureVirtual(self.entity) != 0 }
    }

    /// Is this cursor's referent a struct or class with virtual members?
    pub(crate) fn is_virtual_base(&self) -> bool {
        unsafe { clang_isVirtualBase(self.entity) != 0 }
    }

    /// Try to evaluate this cursor.
    pub(crate) fn evaluate(&self) -> Option<EvalResult> {
        EvalResult::new(*self)
    }

    /// Return the result type for this cursor
    pub(crate) fn ret_type(&self) -> Option<Type> {
        let rt = Type {
            ty: unsafe { clang_getCursorResultType(self.entity) },
        };
        if rt.is_valid() {
            Some(rt)
        } else {
            None
        }
    }

    /// Gets the tokens that correspond to that cursor.
    pub(crate) fn tokens(&self) -> RawTokens {
        RawTokens::new(self)
    }

    /// Gets the tokens that correspond to that cursor as  `cexpr` tokens.
    pub(crate) fn cexpr_tokens(self) -> Vec<cexpr::token::Token> {
        self.tokens()
            .iter()
            .filter_map(|token| token.as_cexpr_token())
            .collect()
    }

    /// Obtain the real path name of a cursor of InclusionDirective kind.
    ///
    /// Returns None if the cursor does not include a file, otherwise the file's full name
    pub(crate) fn get_included_file_name(&self) -> Option<String> {
        let file = unsafe { clang_sys::clang_getIncludedFile(self.entity) };
        if file.is_null() {
            None
        } else {
            Some(unsafe {
                cxstring_into_string(clang_sys::clang_getFileName(file))
            })
        }
    }
}

/// A struct that owns the tokenizer result from a given cursor.
pub(crate) struct RawTokens<'a> {
    cursor: &'a Cursor,
    tu: CXTranslationUnit,
    tokens: *mut CXToken,
    token_count: c_uint,
}

impl<'a> RawTokens<'a> {
    fn new(cursor: &'a Cursor) -> Self {
        let mut tokens = ptr::null_mut();
        let mut token_count = 0;
        let range = cursor.extent();
        let tu = unsafe { clang_Cursor_getTranslationUnit(cursor.entity) };
        unsafe { clang_tokenize(tu, range, &mut tokens, &mut token_count) };
        Self {
            cursor,
            tu,
            tokens,
            token_count,
        }
    }

    fn as_slice(&self) -> &[CXToken] {
        if self.tokens.is_null() {
            return &[];
        }
        unsafe { slice::from_raw_parts(self.tokens, self.token_count as usize) }
    }

    /// Get an iterator over these tokens.
    pub(crate) fn iter(&self) -> ClangTokenIterator {
        ClangTokenIterator {
            tu: self.tu,
            raw: self.as_slice().iter(),
        }
    }
}

impl<'a> Drop for RawTokens<'a> {
    fn drop(&mut self) {
        if !self.tokens.is_null() {
            unsafe {
                clang_disposeTokens(
                    self.tu,
                    self.tokens,
                    self.token_count as c_uint,
                );
            }
        }
    }
}

/// A raw clang token, that exposes only kind, spelling, and extent. This is a
/// slightly more convenient version of `CXToken` which owns the spelling
/// string and extent.
#[derive(Debug)]
pub(crate) struct ClangToken {
    spelling: CXString,
    /// The extent of the token. This is the same as the relevant member from
    /// `CXToken`.
    pub(crate) extent: CXSourceRange,
    /// The kind of the token. This is the same as the relevant member from
    /// `CXToken`.
    pub(crate) kind: CXTokenKind,
}

impl ClangToken {
    /// Get the token spelling, without being converted to utf-8.
    pub(crate) fn spelling(&self) -> &[u8] {
        let c_str = unsafe {
            CStr::from_ptr(clang_getCString(self.spelling) as *const _)
        };
        c_str.to_bytes()
    }

    /// Converts a ClangToken to a `cexpr` token if possible.
    pub(crate) fn as_cexpr_token(&self) -> Option<cexpr::token::Token> {
        use cexpr::token;

        let kind = match self.kind {
            CXToken_Punctuation => token::Kind::Punctuation,
            CXToken_Literal => token::Kind::Literal,
            CXToken_Identifier => token::Kind::Identifier,
            CXToken_Keyword => token::Kind::Keyword,
            // NB: cexpr is not too happy about comments inside
            // expressions, so we strip them down here.
            CXToken_Comment => return None,
            _ => {
                warn!("Found unexpected token kind: {:?}", self);
                return None;
            }
        };

        Some(token::Token {
            kind,
            raw: self.spelling().to_vec().into_boxed_slice(),
        })
    }
}

impl Drop for ClangToken {
    fn drop(&mut self) {
        unsafe { clang_disposeString(self.spelling) }
    }
}

/// An iterator over a set of Tokens.
pub(crate) struct ClangTokenIterator<'a> {
    tu: CXTranslationUnit,
    raw: slice::Iter<'a, CXToken>,
}

impl<'a> Iterator for ClangTokenIterator<'a> {
    type Item = ClangToken;

    fn next(&mut self) -> Option<Self::Item> {
        let raw = self.raw.next()?;
        unsafe {
            let kind = clang_getTokenKind(*raw);
            let spelling = clang_getTokenSpelling(self.tu, *raw);
            let extent = clang_getTokenExtent(self.tu, *raw);
            Some(ClangToken {
                kind,
                extent,
                spelling,
            })
        }
    }
}

/// Checks whether the name looks like an identifier, i.e. is alphanumeric
/// (including '_') and does not start with a digit.
pub(crate) fn is_valid_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    let first_valid = chars
        .next()
        .map(|c| c.is_alphabetic() || c == '_')
        .unwrap_or(false);

    first_valid && chars.all(|c| c.is_alphanumeric() || c == '_')
}

extern "C" fn visit_children<Visitor>(
    cur: CXCursor,
    _parent: CXCursor,
    data: CXClientData,
) -> EntityVisitResult
where
    Visitor: FnMut(Cursor) -> EntityVisitResult,
{
    let func: &mut Visitor = unsafe { &mut *(data as *mut Visitor) };
    let child = Cursor { entity: cur };

    (*func)(child)
}

impl PartialEq for Cursor {
    fn eq(&self, other: &Cursor) -> bool {
        unsafe { clang_equalCursors(self.entity, other.entity) == 1 }
    }
}

impl Eq for Cursor {}

impl Hash for Cursor {
    fn hash<H: Hasher>(&self, state: &mut H) {
        unsafe { clang_hashCursor(self.entity) }.hash(state)
    }
}

/// The type of a node in clang's AST.
#[derive(Clone, Copy)]
pub(crate) struct Type<'tu> {
    ty: Option<clang::Type<'tu>>,
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        unsafe { clang_equalTypes(self.ty, other.ty) != 0 }
    }
}

impl Eq for Type {}

impl fmt::Debug for Type {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(
            fmt,
            "Type({}, kind: {}, cconv: {}, decl: {:?}, canon: {:?})",
            self.spelling(),
            type_to_str(self.kind()),
            self.call_conv(),
            self.declaration(),
            self.declaration().canonical()
        )
    }
}

/// An error about the layout of a struct, class, or type.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub(crate) enum LayoutError {
    /// Asked for the layout of an invalid type.
    Invalid,
    /// Asked for the layout of an incomplete type.
    Incomplete,
    /// Asked for the layout of a dependent type.
    Dependent,
    /// Asked for the layout of a type that does not have constant size.
    NotConstantSize,
    /// Asked for the layout of a field in a type that does not have such a
    /// field.
    InvalidFieldName,
    /// An unknown layout error.
    Unknown,
}

impl ::std::convert::From<i32> for LayoutError {
    fn from(val: i32) -> Self {
        use self::LayoutError::*;

        match val {
            CXTypeLayoutError_Invalid => Invalid,
            CXTypeLayoutError_Incomplete => Incomplete,
            CXTypeLayoutError_Dependent => Dependent,
            CXTypeLayoutError_NotConstantSize => NotConstantSize,
            CXTypeLayoutError_InvalidFieldName => InvalidFieldName,
            _ => Unknown,
        }
    }
}

impl Type {
    /// Get this type's kind.
    pub(crate) fn kind(&self) -> CXTypeKind {
        self.ty.kind
    }

    /// Get a cursor pointing to this type's declaration.
    pub(crate) fn declaration(&self) -> Cursor {
        unsafe {
            Cursor {
                entity: clang_getTypeDeclaration(self.ty),
            }
        }
    }

    /// Get the canonical declaration of this type, if it is available.
    pub(crate) fn canonical_declaration(
        &self,
        location: Option<&Cursor>,
    ) -> Option<CanonicalTypeDeclaration> {
        let mut declaration = self.declaration();
        if !declaration.is_valid() {
            if let Some(location) = location {
                let mut location = *location;
                if let Some(referenced) = location.referenced() {
                    location = referenced;
                }
                if location.is_template_like() {
                    declaration = location;
                }
            }
        }

        let canonical = declaration.canonical();
        if canonical.is_valid() && canonical.kind() != EntityKind::NoDeclFound {
            Some(CanonicalTypeDeclaration(*self, canonical))
        } else {
            None
        }
    }

    /// Get a raw display name for this type.
    pub(crate) fn spelling(&self) -> String {
        let s = unsafe { cxstring_into_string(clang_getTypeSpelling(self.ty)) };
        // Clang 5.0 introduced changes in the spelling API so it returned the
        // full qualified name. Let's undo that here.
        if s.split("::").all(is_valid_identifier) {
            if let Some(s) = s.split("::").last() {
                return s.to_owned();
            }
        }

        s
    }

    /// Is this type const qualified?
    pub(crate) fn is_const(&self) -> bool {
        unsafe { clang_isConstQualifiedType(self.ty) != 0 }
    }

    #[inline]
    fn is_non_deductible_auto_type(&self) -> bool {
        debug_assert_eq!(self.kind(), clang::TypeKind::Auto);
        self.canonical_type() == *self
    }

    #[inline]
    fn clang_size_of(&self, ctx: &BindgenContext) -> c_longlong {
        match self.kind() {
            // Work-around https://bugs.llvm.org/show_bug.cgi?id=40975
            clang::TypeKind::RValueReference |
            clang::TypeKind::LValueReference => {
                ctx.target_pointer_size() as c_longlong
            }
            // Work-around https://bugs.llvm.org/show_bug.cgi?id=40813
            clang::TypeKind::Auto if self.is_non_deductible_auto_type() => -6,
            _ => unsafe { clang_Type_getSizeOf(self.ty) },
        }
    }

    #[inline]
    fn clang_align_of(&self, ctx: &BindgenContext) -> c_longlong {
        match self.kind() {
            // Work-around https://bugs.llvm.org/show_bug.cgi?id=40975
            clang::TypeKind::RValueReference |
            clang::TypeKind::LValueReference => {
                ctx.target_pointer_size() as c_longlong
            }
            // Work-around https://bugs.llvm.org/show_bug.cgi?id=40813
            clang::TypeKind::Auto if self.is_non_deductible_auto_type() => -6,
            _ => unsafe { clang_Type_getAlignOf(self.ty) },
        }
    }

    /// What is the size of this type? Paper over invalid types by returning `0`
    /// for them.
    pub(crate) fn size(&self, ctx: &BindgenContext) -> usize {
        let val = self.clang_size_of(ctx);
        if val < 0 {
            0
        } else {
            val as usize
        }
    }

    /// What is the size of this type?
    pub(crate) fn fallible_size(
        &self,
        ctx: &BindgenContext,
    ) -> Result<usize, LayoutError> {
        let val = self.clang_size_of(ctx);
        if val < 0 {
            Err(LayoutError::from(val as i32))
        } else {
            Ok(val as usize)
        }
    }

    /// What is the alignment of this type? Paper over invalid types by
    /// returning `0`.
    pub(crate) fn align(&self, ctx: &BindgenContext) -> usize {
        let val = self.clang_align_of(ctx);
        if val < 0 {
            0
        } else {
            val as usize
        }
    }

    /// What is the alignment of this type?
    pub(crate) fn fallible_align(
        &self,
        ctx: &BindgenContext,
    ) -> Result<usize, LayoutError> {
        let val = self.clang_align_of(ctx);
        if val < 0 {
            Err(LayoutError::from(val as i32))
        } else {
            Ok(val as usize)
        }
    }

    /// Get the layout for this type, or an error describing why it does not
    /// have a valid layout.
    pub(crate) fn fallible_layout(
        &self,
        ctx: &BindgenContext,
    ) -> Result<crate::ir::layout::Layout, LayoutError> {
        use crate::ir::layout::Layout;
        let size = self.fallible_size(ctx)?;
        let align = self.fallible_align(ctx)?;
        Ok(Layout::new(size, align))
    }

    /// Get the number of template arguments this type has, or `None` if it is
    /// not some kind of template.
    pub(crate) fn num_template_args(&self) -> Option<u32> {
        let n = unsafe { clang_Type_getNumTemplateArguments(self.ty) };
        if n >= 0 {
            Some(n as u32)
        } else {
            debug_assert_eq!(n, -1);
            None
        }
    }

    /// If this type is a class template specialization, return its
    /// template arguments. Otherwise, return None.
    pub(crate) fn template_args(&self) -> Option<TypeTemplateArgIterator> {
        self.num_template_args().map(|n| TypeTemplateArgIterator {
            x: self.ty,
            length: n,
            index: 0,
        })
    }

    /// Given that this type is a function prototype, return the types of its parameters.
    ///
    /// Returns None if the type is not a function prototype.
    pub(crate) fn args(&self) -> Option<Vec<Type>> {
        self.num_args().ok().map(|num| {
            (0..num)
                .map(|i| Type {
                    ty: unsafe { clang_getArgType(self.ty, i as c_uint) },
                })
                .collect()
        })
    }

    /// Given that this type is a function prototype, return the number of arguments it takes.
    ///
    /// Returns Err if the type is not a function prototype.
    pub(crate) fn num_args(&self) -> Result<u32, ()> {
        unsafe {
            let w = clang_getNumArgTypes(self.ty);
            if w == -1 {
                Err(())
            } else {
                Ok(w as u32)
            }
        }
    }

    /// Given that this type is a pointer type, return the type that it points
    /// to.
    pub(crate) fn pointee_type(&self) -> Option<Type> {
        match self.kind() {
            clang::TypeKind::Pointer |
            clang::TypeKind::RValueReference |
            clang::TypeKind::LValueReference |
            clang::TypeKind::MemberPointer |
            clang::TypeKind::BlockPointer |
            clang::TypeKind::ObjCObjectPointer => {
                let ret = Type {
                    ty: unsafe { clang_getPointeeType(self.ty) },
                };
                debug_assert!(ret.is_valid());
                Some(ret)
            }
            _ => None,
        }
    }

    /// Given that this type is an array, vector, or complex type, return the
    /// type of its elements.
    pub(crate) fn elem_type(&self) -> Option<Type> {
        let current_type = Type {
            ty: unsafe { clang_getElementType(self.ty) },
        };
        if current_type.is_valid() {
            Some(current_type)
        } else {
            None
        }
    }

    /// Given that this type is an array or vector type, return its number of
    /// elements.
    pub(crate) fn num_elements(&self) -> Option<usize> {
        let num_elements_returned = unsafe { clang_getNumElements(self.ty) };
        if num_elements_returned != -1 {
            Some(num_elements_returned as usize)
        } else {
            None
        }
    }

    /// Get the canonical version of this type. This sees through `typedef`s and
    /// aliases to get the underlying, canonical type.
    pub(crate) fn canonical_type(&self) -> Type {
        unsafe {
            Type {
                ty: clang_getCanonicalType(self.ty),
            }
        }
    }

    /// Is this type a variadic function type?
    pub(crate) fn is_variadic(&self) -> bool {
        unsafe { clang_isFunctionTypeVariadic(self.ty) != 0 }
    }

    /// Given that this type is a function type, get the type of its return
    /// value.
    pub(crate) fn ret_type(&self) -> Option<Type> {
        let rt = Type {
            ty: unsafe { clang_getResultType(self.ty) },
        };
        if rt.is_valid() {
            Some(rt)
        } else {
            None
        }
    }

    /// Given that this type is a function type, get its calling convention. If
    /// this is not a function type, `CXCallingConv_Invalid` is returned.
    pub(crate) fn call_conv(&self) -> CXCallingConv {
        unsafe { clang_getFunctionTypeCallingConv(self.ty) }
    }

    /// For elaborated types (types which use `class`, `struct`, or `union` to
    /// disambiguate types from local bindings), get the underlying type.
    pub(crate) fn named(&self) -> Type {
        unsafe {
            Type {
                ty: clang_Type_getNamedType(self.ty),
            }
        }
    }

    /// Is this a valid type?
    pub(crate) fn is_valid(&self) -> bool {
        self.kind() != clang::TypeKind::Invalid
    }

    /// Is this a valid and exposed type?
    pub(crate) fn is_valid_and_exposed(&self) -> bool {
        self.is_valid() && self.kind() != clang::TypeKind::Unexposed
    }

    /// Is this type a fully instantiated template?
    pub(crate) fn is_fully_instantiated_template(&self) -> bool {
        // Yep, the spelling of this containing type-parameter is extremely
        // nasty... But can happen in <type_traits>. Unfortunately I couldn't
        // reduce it enough :(
        self.template_args().map_or(false, |args| args.len() > 0) &&
            !matches!(
                self.declaration().kind(),
                EntityKind::ClassTemplatePartialSpecialization |
                    EntityKind::TypeAliasTemplateDecl |
                    EntityKind::TemplateTemplateParameter
            )
    }

    /// Is this type an associated template type? Eg `T::Associated` in
    /// this example:
    ///
    /// ```c++
    /// template <typename T>
    /// class Foo {
    ///     typename T::Associated member;
    /// };
    /// ```
    pub(crate) fn is_associated_type(&self) -> bool {
        // This is terrible :(
        fn hacky_parse_associated_type<S: AsRef<str>>(spelling: S) -> bool {
            lazy_static! {
                static ref ASSOC_TYPE_RE: regex::Regex = regex::Regex::new(
                    r"typename type\-parameter\-\d+\-\d+::.+"
                )
                .unwrap();
            }
            ASSOC_TYPE_RE.is_match(spelling.as_ref())
        }

        self.kind() == clang::TypeKind::Unexposed &&
            (hacky_parse_associated_type(self.spelling()) ||
                hacky_parse_associated_type(
                    self.canonical_type().spelling(),
                ))
    }
}

/// The `CanonicalTypeDeclaration` type exists as proof-by-construction that its
/// cursor is the canonical declaration for its type. If you have a
/// `CanonicalTypeDeclaration` instance, you know for sure that the type and
/// cursor match up in a canonical declaration relationship, and it simply
/// cannot be otherwise.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CanonicalTypeDeclaration(Type, Cursor);

impl CanonicalTypeDeclaration {
    /// Get the type.
    pub(crate) fn ty(&self) -> &Type {
        &self.0
    }

    /// Get the type's canonical declaration cursor.
    pub(crate) fn cursor(&self) -> &Cursor {
        &self.1
    }
}

/// An iterator for a type's template arguments.
pub(crate) struct TypeTemplateArgIterator {
    x: CXType,
    length: u32,
    index: u32,
}

impl Iterator for TypeTemplateArgIterator {
    type Item = Type;
    fn next(&mut self) -> Option<Type> {
        if self.index < self.length {
            let idx = self.index as c_uint;
            self.index += 1;
            Some(Type {
                ty: unsafe {
                    clang_Type_getTemplateArgumentAsType(self.x, idx)
                },
            })
        } else {
            None
        }
    }
}

impl ExactSizeIterator for TypeTemplateArgIterator {
    fn len(&self) -> usize {
        assert!(self.index <= self.length);
        (self.length - self.index) as usize
    }
}

/// A `SourceLocation` is a file, line, column, and byte offset location for
/// some source text.
pub(crate) struct SourceLocation {
    location: CXSourceLocation,
}

impl SourceLocation {
    /// Get the (file, line, column, byte offset) tuple for this source
    /// location.
    pub(crate) fn location(&self) -> (File, usize, usize, usize) {
        unsafe {
            let mut file = mem::zeroed();
            let mut line = 0;
            let mut col = 0;
            let mut off = 0;
            clang_getSpellingLocation(
                self.location,
                &mut file,
                &mut line,
                &mut col,
                &mut off,
            );
            (File { x: file }, line as usize, col as usize, off as usize)
        }
    }
}

impl fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (file, line, col, _) = self.location();
        if let Some(name) = file.name() {
            write!(f, "{}:{}:{}", name, line, col)
        } else {
            "builtin definitions".fmt(f)
        }
    }
}

impl fmt::Debug for SourceLocation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

/// A comment in the source text.
///
/// Comments are sort of parsed by Clang, and have a tree structure.
pub(crate) struct Comment<'tu> {
    comment: Option<clang::Comment<'tu>>,
}

impl Comment {
    /// What kind of comment is this?
    pub(crate) fn kind(&self) -> CXCommentKind {
        unsafe { clang_Comment_getKind(self.comment) }
    }

    /// Get this comment's children comment
    pub(crate) fn get_children(&self) -> CommentChildrenIterator {
        CommentChildrenIterator {
            parent: self.comment,
            length: unsafe { clang_Comment_getNumChildren(self.comment) },
            index: 0,
        }
    }

    /// Given that this comment is the start or end of an HTML tag, get its tag
    /// name.
    pub(crate) fn get_tag_name(&self) -> String {
        unsafe {
            cxstring_into_string(clang_HTMLTagComment_getTagName(self.comment))
        }
    }

    /// Given that this comment is an HTML start tag, get its attributes.
    pub(crate) fn get_tag_attrs(&self) -> CommentAttributesIterator {
        CommentAttributesIterator {
            x: self.comment,
            length: unsafe { clang_HTMLStartTag_getNumAttrs(self.comment) },
            index: 0,
        }
    }
}

/// An iterator for a comment's children
pub(crate) struct CommentChildrenIterator {
    parent: CXComment,
    length: c_uint,
    index: c_uint,
}

impl Iterator for CommentChildrenIterator {
    type Item = Comment;
    fn next(&mut self) -> Option<Comment> {
        if self.index < self.length {
            let idx = self.index;
            self.index += 1;
            Some(Comment {
                comment: unsafe { clang_Comment_getChild(self.parent, idx) },
            })
        } else {
            None
        }
    }
}

/// An HTML start tag comment attribute
pub(crate) struct CommentAttribute {
    /// HTML start tag attribute name
    pub(crate) name: String,
    /// HTML start tag attribute value
    pub(crate) value: String,
}

/// An iterator for a comment's attributes
pub(crate) struct CommentAttributesIterator {
    x: CXComment,
    length: c_uint,
    index: c_uint,
}

impl Iterator for CommentAttributesIterator {
    type Item = CommentAttribute;
    fn next(&mut self) -> Option<CommentAttribute> {
        if self.index < self.length {
            let idx = self.index;
            self.index += 1;
            Some(CommentAttribute {
                name: unsafe {
                    cxstring_into_string(clang_HTMLStartTag_getAttrName(
                        self.x, idx,
                    ))
                },
                value: unsafe {
                    cxstring_into_string(clang_HTMLStartTag_getAttrValue(
                        self.x, idx,
                    ))
                },
            })
        } else {
            None
        }
    }
}

/// A source file.
pub(crate) struct File {
    x: CXFile,
}

impl File {
    /// Get the name of this source file.
    pub(crate) fn name(&self) -> Option<String> {
        if self.x.is_null() {
            return None;
        }
        Some(unsafe { cxstring_into_string(clang_getFileName(self.x)) })
    }
}

fn cxstring_to_string_leaky(s: CXString) -> String {
    if s.data.is_null() {
        return "".to_owned();
    }
    let c_str = unsafe { CStr::from_ptr(clang_getCString(s) as *const _) };
    c_str.to_string_lossy().into_owned()
}

fn cxstring_into_string(s: CXString) -> String {
    let ret = cxstring_to_string_leaky(s);
    unsafe { clang_disposeString(s) };
    ret
}

/// An `Index` is an environment for a set of translation units that will
/// typically end up linked together in one final binary.
pub(crate) struct Index {
    x: CXIndex,
}

impl Index {
    /// Construct a new `Index`.
    ///
    /// The `pch` parameter controls whether declarations in pre-compiled
    /// headers are included when enumerating a translation unit's "locals".
    ///
    /// The `diag` parameter controls whether debugging diagnostics are enabled.
    pub(crate) fn new(pch: bool, diag: bool) -> Index {
        unsafe {
            Index {
                x: clang_createIndex(pch as c_int, diag as c_int),
            }
        }
    }
}

impl fmt::Debug for Index {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "Index {{ }}")
    }
}

impl Drop for Index {
    fn drop(&mut self) {
        unsafe {
            clang_disposeIndex(self.x);
        }
    }
}

/// A translation unit (or "compilation unit").
pub(crate) struct TranslationUnit {
    x: CXTranslationUnit,
}

impl fmt::Debug for TranslationUnit {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "TranslationUnit {{ }}")
    }
}

impl TranslationUnit {
    /// Parse a source file into a translation unit.
    pub(crate) fn parse(
        ix: &Index,
        file: &str,
        cmd_args: &[String],
        unsaved: &[UnsavedFile],
        opts: CXTranslationUnit_Flags,
    ) -> Option<TranslationUnit> {
        let fname = CString::new(file).unwrap();
        let _c_args: Vec<CString> = cmd_args
            .iter()
            .map(|s| CString::new(s.clone()).unwrap())
            .collect();
        let c_args: Vec<*const c_char> =
            _c_args.iter().map(|s| s.as_ptr()).collect();
        let mut c_unsaved: Vec<CXUnsavedFile> =
            unsaved.iter().map(|f| f.x).collect();
        let tu = unsafe {
            clang_parseTranslationUnit(
                ix.x,
                fname.as_ptr(),
                c_args.as_ptr(),
                c_args.len() as c_int,
                c_unsaved.as_mut_ptr(),
                c_unsaved.len() as c_uint,
                opts,
            )
        };
        if tu.is_null() {
            None
        } else {
            Some(TranslationUnit { x: tu })
        }
    }

    /// Get the Clang diagnostic information associated with this translation
    /// unit.
    pub(crate) fn diags(&self) -> Vec<Diagnostic> {
        unsafe {
            let num = clang_getNumDiagnostics(self.x) as usize;
            let mut diags = vec![];
            for i in 0..num {
                diags.push(Diagnostic {
                    x: clang_getDiagnostic(self.x, i as c_uint),
                });
            }
            diags
        }
    }

    /// Get a cursor pointing to the root of this translation unit's AST.
    pub(crate) fn cursor(&self) -> Cursor {
        unsafe {
            Cursor {
                entity: clang_getTranslationUnitCursor(self.x),
            }
        }
    }

    /// Is this the null translation unit?
    pub(crate) fn is_null(&self) -> bool {
        self.x.is_null()
    }
}

impl Drop for TranslationUnit {
    fn drop(&mut self) {
        unsafe {
            clang_disposeTranslationUnit(self.x);
        }
    }
}

/// A diagnostic message generated while parsing a translation unit.
pub(crate) struct Diagnostic {
    x: CXDiagnostic,
}

impl Diagnostic {
    /// Format this diagnostic message as a string, using the given option bit
    /// flags.
    pub(crate) fn format(&self) -> String {
        unsafe {
            let opts = clang_defaultDiagnosticDisplayOptions();
            cxstring_into_string(clang_formatDiagnostic(self.x, opts))
        }
    }

    /// What is the severity of this diagnostic message?
    pub(crate) fn severity(&self) -> CXDiagnosticSeverity {
        unsafe { clang_getDiagnosticSeverity(self.x) }
    }
}

impl Drop for Diagnostic {
    /// Destroy this diagnostic message.
    fn drop(&mut self) {
        unsafe {
            clang_disposeDiagnostic(self.x);
        }
    }
}

/// A file which has not been saved to disk.
pub(crate) struct UnsavedFile {
    x: CXUnsavedFile,
    /// The name of the unsaved file. Kept here to avoid leaving dangling pointers in
    /// `CXUnsavedFile`.
    pub(crate) name: CString,
    contents: CString,
}

impl UnsavedFile {
    /// Construct a new unsaved file with the given `name` and `contents`.
    pub(crate) fn new(name: String, contents: String) -> UnsavedFile {
        let name = CString::new(name).unwrap();
        let contents = CString::new(contents).unwrap();
        let x = CXUnsavedFile {
            Filename: name.as_ptr(),
            Contents: contents.as_ptr(),
            Length: contents.as_bytes().len() as c_ulong,
        };
        UnsavedFile { x, name, contents }
    }
}

impl fmt::Debug for UnsavedFile {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(
            fmt,
            "UnsavedFile(name: {:?}, contents: {:?})",
            self.name, self.contents
        )
    }
}

/// Convert a cursor kind into a static string.
pub(crate) fn kind_to_str(x: CXCursorKind) -> String {
    unsafe { cxstring_into_string(clang_getCursorKindSpelling(x)) }
}

/// Convert a type kind to a static string.
pub(crate) fn type_to_str(x: CXTypeKind) -> String {
    unsafe { cxstring_into_string(clang_getTypeKindSpelling(x)) }
}

/// Dump the Clang AST to stdout for debugging purposes.
pub(crate) fn ast_dump(c: &Cursor, depth: isize) -> EntityVisitResult {
    fn print_indent<S: AsRef<str>>(depth: isize, s: S) {
        for _ in 0..depth {
            print!("    ");
        }
        println!("{}", s.as_ref());
    }

    fn print_cursor<S: AsRef<str>>(depth: isize, prefix: S, c: &Cursor) {
        let prefix = prefix.as_ref();
        print_indent(
            depth,
            format!(" {}kind = {}", prefix, kind_to_str(c.kind())),
        );
        print_indent(
            depth,
            format!(" {}spelling = \"{}\"", prefix, c.spelling()),
        );
        print_indent(depth, format!(" {}location = {}", prefix, c.location()));
        print_indent(
            depth,
            format!(" {}is-definition? {}", prefix, c.is_definition()),
        );
        print_indent(
            depth,
            format!(" {}is-declaration? {}", prefix, c.is_declaration()),
        );
        print_indent(
            depth,
            format!(
                " {}is-inlined-function? {}",
                prefix,
                c.is_inlined_function()
            ),
        );

        let templ_kind = c.template_kind();
        if templ_kind != EntityKind::NoDeclFound {
            print_indent(
                depth,
                format!(
                    " {}template-kind = {}",
                    prefix,
                    kind_to_str(templ_kind)
                ),
            );
        }
        if let Some(usr) = c.usr() {
            print_indent(depth, format!(" {}usr = \"{}\"", prefix, usr));
        }
        if let Ok(num) = c.num_args() {
            print_indent(depth, format!(" {}number-of-args = {}", prefix, num));
        }
        if let Some(num) = c.num_template_args() {
            print_indent(
                depth,
                format!(" {}number-of-template-args = {}", prefix, num),
            );
        }

        if c.is_bit_field() {
            let width = match c.bit_width() {
                Some(w) => w.to_string(),
                None => "<unevaluable>".to_string(),
            };
            print_indent(depth, format!(" {}bit-width = {}", prefix, width));
        }

        if let Some(ty) = c.enum_type() {
            print_indent(
                depth,
                format!(" {}enum-type = {}", prefix, type_to_str(ty.kind())),
            );
        }
        if let Some(val) = c.enum_val_signed() {
            print_indent(depth, format!(" {}enum-val = {}", prefix, val));
        }
        if let Some(ty) = c.typedef_type() {
            print_indent(
                depth,
                format!(" {}typedef-type = {}", prefix, type_to_str(ty.kind())),
            );
        }
        if let Some(ty) = c.ret_type() {
            print_indent(
                depth,
                format!(" {}ret-type = {}", prefix, type_to_str(ty.kind())),
            );
        }

        if let Some(refd) = c.referenced() {
            if refd != *c {
                println!();
                print_cursor(
                    depth,
                    String::from(prefix) + "referenced.",
                    &refd,
                );
            }
        }

        let canonical = c.canonical();
        if canonical != *c {
            println!();
            print_cursor(
                depth,
                String::from(prefix) + "canonical.",
                &canonical,
            );
        }

        if let Some(specialized) = c.specialized() {
            if specialized != *c {
                println!();
                print_cursor(
                    depth,
                    String::from(prefix) + "specialized.",
                    &specialized,
                );
            }
        }

        if let Some(parent) = c.fallible_semantic_parent() {
            println!();
            print_cursor(
                depth,
                String::from(prefix) + "semantic-parent.",
                &parent,
            );
        }
    }

    fn print_type<S: AsRef<str>>(depth: isize, prefix: S, ty: &Type) {
        let prefix = prefix.as_ref();

        let kind = ty.kind();
        print_indent(depth, format!(" {}kind = {}", prefix, type_to_str(kind)));
        if kind == clang::TypeKind::Invalid {
            return;
        }

        print_indent(depth, format!(" {}cconv = {}", prefix, ty.call_conv()));

        print_indent(
            depth,
            format!(" {}spelling = \"{}\"", prefix, ty.spelling()),
        );
        let num_template_args =
            unsafe { clang_Type_getNumTemplateArguments(ty.ty) };
        if num_template_args >= 0 {
            print_indent(
                depth,
                format!(
                    " {}number-of-template-args = {}",
                    prefix, num_template_args
                ),
            );
        }
        if let Some(num) = ty.num_elements() {
            print_indent(
                depth,
                format!(" {}number-of-elements = {}", prefix, num),
            );
        }
        print_indent(
            depth,
            format!(" {}is-variadic? {}", prefix, ty.is_variadic()),
        );

        let canonical = ty.canonical_type();
        if canonical != *ty {
            println!();
            print_type(depth, String::from(prefix) + "canonical.", &canonical);
        }

        if let Some(pointee) = ty.pointee_type() {
            if pointee != *ty {
                println!();
                print_type(depth, String::from(prefix) + "pointee.", &pointee);
            }
        }

        if let Some(elem) = ty.elem_type() {
            if elem != *ty {
                println!();
                print_type(depth, String::from(prefix) + "elements.", &elem);
            }
        }

        if let Some(ret) = ty.ret_type() {
            if ret != *ty {
                println!();
                print_type(depth, String::from(prefix) + "return.", &ret);
            }
        }

        let named = ty.named();
        if named != *ty && named.is_valid() {
            println!();
            print_type(depth, String::from(prefix) + "named.", &named);
        }
    }

    print_indent(depth, "(");
    print_cursor(depth, "", c);

    println!();
    let ty = c.cur_type();
    print_type(depth, "type.", &ty);

    let declaration = ty.declaration();
    if declaration != *c && declaration.kind() != EntityKind::NoDeclFound {
        println!();
        print_cursor(depth, "type.declaration.", &declaration);
    }

    // Recurse.
    let mut found_children = false;
    c.visit(|s| {
        if !found_children {
            println!();
            found_children = true;
        }
        ast_dump(&s, depth + 1)
    });

    print_indent(depth, ")");

    EntityVisitResult::Continue
}

/// Try to extract the clang version to a string
pub(crate) fn extract_clang_version() -> String {
    unsafe { cxstring_into_string(clang_getClangVersion()) }
}

/// A wrapper for the result of evaluating an expression.
#[derive(Debug)]
pub(crate) struct EvalResult {
    x: CXEvalResult,
    ty: Type,
}

impl EvalResult {
    /// Evaluate `cursor` and return the result.
    pub(crate) fn new(cursor: Cursor) -> Option<Self> {
        // Work around https://bugs.llvm.org/show_bug.cgi?id=42532, see:
        //  * https://github.com/rust-lang/rust-bindgen/issues/283
        //  * https://github.com/rust-lang/rust-bindgen/issues/1590
        {
            let mut found_cant_eval = false;
            cursor.visit(|c| {
                if c.kind() == Some(EntityKind::TypeRef) &&
                    c.cur_type().canonical_type().kind() ==
                        clang::TypeKind::Unexposed
                {
                    found_cant_eval = true;
                    return EntityVisitResult::Break;
                }

                EntityVisitResult::Recurse
            });

            if found_cant_eval {
                return None;
            }
        }
        Some(EvalResult {
            x: unsafe { clang_Cursor_Evaluate(cursor.entity) },
            ty: cursor.cur_type().canonical_type(),
        })
    }

    fn kind(&self) -> CXEvalResultKind {
        unsafe { clang_EvalResult_getKind(self.x) }
    }

    /// Try to get back the result as a double.
    pub(crate) fn as_double(&self) -> Option<f64> {
        match self.kind() {
            CXEval_Float => {
                Some(unsafe { clang_EvalResult_getAsDouble(self.x) })
            }
            _ => None,
        }
    }

    /// Try to get back the result as an integer.
    pub(crate) fn as_int(&self) -> Option<i64> {
        if self.kind() != CXEval_Int {
            return None;
        }

        if unsafe { clang_EvalResult_isUnsignedInt(self.x) } != 0 {
            let value = unsafe { clang_EvalResult_getAsUnsigned(self.x) };
            if value > i64::max_value() as c_ulonglong {
                return None;
            }

            return Some(value as i64);
        }

        let value = unsafe { clang_EvalResult_getAsLongLong(self.x) };
        if value > i64::max_value() as c_longlong {
            return None;
        }
        if value < i64::min_value() as c_longlong {
            return None;
        }
        #[allow(clippy::unnecessary_cast)]
        Some(value as i64)
    }

    /// Evaluates the expression as a literal string, that may or may not be
    /// valid utf-8.
    pub(crate) fn as_literal_string(&self) -> Option<Vec<u8>> {
        if self.kind() != CXEval_StrLiteral {
            return None;
        }

        let char_ty = self.ty.pointee_type().or_else(|| self.ty.elem_type())?;
        match char_ty.kind() {
            clang::TypeKind::Char_S |
            clang::TypeKind::SChar |
            clang::TypeKind::Char_U |
            clang::TypeKind::UChar => {
                let ret = unsafe {
                    CStr::from_ptr(clang_EvalResult_getAsStr(self.x))
                };
                Some(ret.to_bytes().to_vec())
            }
            // FIXME: Support generating these.
            clang::TypeKind::Char16 => None,
            clang::TypeKind::Char32 => None,
            clang::TypeKind::WChar => None,
            _ => None,
        }
    }
}

impl Drop for EvalResult {
    fn drop(&mut self) {
        unsafe { clang_EvalResult_dispose(self.x) };
    }
}

/// Target information obtained from libclang.
#[derive(Debug)]
pub(crate) struct TargetInfo {
    /// The target triple.
    pub(crate) triple: String,
    /// The width of the pointer _in bits_.
    pub(crate) pointer_width: usize,
}

impl TargetInfo {
    /// Tries to obtain target information from libclang.
    pub(crate) fn new(tu: &TranslationUnit) -> Self {
        let triple;
        let pointer_width;
        unsafe {
            let ti = clang_getTranslationUnitTargetInfo(tu.x);
            triple = cxstring_into_string(clang_TargetInfo_getTriple(ti));
            pointer_width = clang_TargetInfo_getPointerWidth(ti);
            clang_TargetInfo_dispose(ti);
        }
        assert!(pointer_width > 0);
        assert_eq!(pointer_width % 8, 0);
        TargetInfo {
            triple,
            pointer_width: pointer_width as usize,
        }
    }
}
