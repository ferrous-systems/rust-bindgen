//! A higher level Clang API built on top of the generated bindings in the
//! `clang_sys` module.

#![allow(non_upper_case_globals, dead_code)]
#![deny(clippy::missing_docs_in_private_items)]

use crate::ir::context::BindgenContext;
use std::ffi::CStr;
use std::hash::Hash;
use std::path::PathBuf;

pub(crate) use clang::diagnostic::Diagnostic;
pub(crate) use clang::documentation::Comment;
pub(crate) use clang::source::{File, SourceLocation};
use clang::token::TokenKind;
use clang::{Entity, EntityKind, TypeKind};
pub(crate) use clang::{Index, TranslationUnit, Type};
use clang_sys::{
    clang_disposeString, clang_getCString, clang_getCursorKindSpelling,
    clang_getTypeKindSpelling, CXString,
};

/// Type representing a clang attribute.
///
/// Values of this type can be used to check for different attributes using the `has_attrs`
/// function.
pub(crate) struct Attribute {
    name: &'static str,
    kind: Option<EntityKind>,
    token_kind: TokenKind,
}

impl Attribute {
    /// A `warn_unused_result` attribute.
    pub(crate) const MUST_USE: Self = Self {
        name: "warn_unused_result",
        kind: Some(EntityKind::WarnUnusedResultAttr),
        token_kind: TokenKind::Identifier,
    };

    /// A `_Noreturn` attribute.
    pub(crate) const NO_RETURN: Self = Self {
        name: "_Noreturn",
        kind: None,
        token_kind: TokenKind::Keyword,
    };

    /// A `[[noreturn]]` attribute.
    pub(crate) const NO_RETURN_CPP: Self = Self {
        name: "noreturn",
        kind: None,
        token_kind: TokenKind::Identifier,
    };
}

pub(crate) trait EntityExt<'tu> {
    fn entity(self) -> Entity<'tu>;
    /// Get the Unified Symbol Resolution for this cursor's referent, if
    /// available.
    ///
    /// The USR can be used to compare entities across translation units.
    fn usr(&self) -> Option<String> {
        self.entity().get_usr().map(|u| u.0)
    }

    /// Is this cursor's referent a declaration?
    fn is_declaration(&self) -> bool {
        self.entity().is_declaration()
    }

    /// Is this cursor's referent an anonymous record or so?
    fn is_anonymous(&self) -> bool {
        self.entity().is_anonymous()
    }

    /// Get this cursor's referent's spelling.
    fn spelling(&self) -> String {
        self.entity().get_name().unwrap_or_default()
    }

    /// Get this cursor's referent's display name.
    ///
    /// This is not necessarily a valid identifier. It includes extra
    /// information, such as parameters for a function, etc.
    fn display_name(&self) -> Option<String> {
        self.entity().get_display_name()
    }

    /// Get the mangled name of this cursor's referent.
    fn mangling(&self) -> String {
        self.entity().get_mangled_name().unwrap_or_default()
    }

    /// Gets the C++ manglings for this cursor, or an error if the manglings
    /// are not available.
    fn cxx_manglings(&self) -> Option<Vec<String>> {
        self.entity().get_mangled_names()
    }

    /// Returns whether the cursor refers to a built-in definition.
    fn is_builtin(&self) -> bool {
        self.entity().get_location().is_none()
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
    fn lexical_parent(&self) -> Option<Cursor<'tu>> {
        self.entity().get_lexical_parent()
    }

    /// Get the referent's semantic parent, if one is available.
    ///
    /// See documentation for `lexical_parent` for details on semantic vs
    /// lexical parents.
    fn fallible_semantic_parent(&self) -> Option<Cursor<'tu>> {
        self.entity().get_semantic_parent()
    }

    /// Get the referent's semantic parent.
    ///
    /// See documentation for `lexical_parent` for details on semantic vs
    /// lexical parents.
    fn semantic_parent(&self) -> Cursor<'tu> {
        self.fallible_semantic_parent().unwrap()
    }

    /// Return the number of template arguments used by this cursor's referent,
    /// if the referent is either a template instantiation. Returns `None`
    /// otherwise.
    ///
    /// NOTE: This may not return `Some` for partial template specializations,
    /// see #193 and #194.
    fn num_template_args(&self) -> Option<usize> {
        self.entity()
            .get_template_arguments()
            .map(|args| args.len())
    }

    /// Get a cursor pointing to this referent's containing translation unit.
    ///
    /// Note that we shouldn't create a `TranslationUnit` struct here, because
    /// bindgen assumes there will only be one of them alive at a time, and
    /// disposes it on drop. That can change if this would be required, but I
    /// think we can survive fine without it.
    fn translation_unit(&self) -> Cursor<'tu> {
        self.entity().get_translation_unit().get_entity()
    }

    /// Is the referent a top level construct?
    fn is_toplevel(&self) -> bool {
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
    fn is_template_like(&self) -> bool {
        matches!(
            self.kind(),
            clang::EntityKind::ClassTemplate |
                clang::EntityKind::ClassTemplatePartialSpecialization |
                clang::EntityKind::TypeAliasTemplateDecl
        )
    }

    /// Is this Cursor pointing to a function-like macro definition?
    fn is_macro_function_like(&self) -> bool {
        self.entity().is_function_like_macro()
    }

    /// Get the kind of referent this cursor is pointing to.
    fn kind(&self) -> EntityKind {
        self.entity().get_kind()
    }

    /// Returns true if the cursor is a definition
    fn is_definition(&self) -> bool {
        self.entity().is_definition()
    }

    /// Is the referent a template specialization?
    fn is_template_specialization(&self) -> bool {
        self.specialized().is_some()
    }

    /// Is the referent a fully specialized template specialization without any
    /// remaining free template arguments?
    fn is_fully_specialized_template(&self) -> bool {
        self.is_template_specialization() &&
            self.kind() != EntityKind::ClassTemplatePartialSpecialization &&
            self.num_template_args().unwrap_or(0) > 0
    }

    /// Is the referent a template specialization that still has remaining free
    /// template arguments?
    fn is_in_non_fully_specialized_template(&self) -> bool {
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
    fn is_template_parameter(&self) -> bool {
        matches!(
            self.kind(),
            clang::EntityKind::TemplateTemplateParameter |
                clang::EntityKind::TemplateTypeParameter |
                clang::EntityKind::NonTypeTemplateParameter
        )
    }

    /// Does the referent's type or value depend on a template parameter?
    fn is_dependent_on_template_parameter(&self) -> bool {
        fn visitor(
            found_template_parameter: &mut bool,
            cur: Cursor,
        ) -> clang::EntityVisitResult {
            // If we found a template parameter, it is dependent.
            if cur.is_template_parameter() {
                *found_template_parameter = true;
                return clang::EntityVisitResult::Break;
            }

            // Get the referent and traverse it as well.
            if let Some(referenced) = cur.referenced() {
                if referenced.is_template_parameter() {
                    *found_template_parameter = true;
                    return clang::EntityVisitResult::Break;
                }

                referenced
                    .visit(|next| visitor(found_template_parameter, next));
                if *found_template_parameter {
                    return clang::EntityVisitResult::Break;
                }
            }

            // Continue traversing the AST at the original cursor.
            clang::EntityVisitResult::Recurse
        }

        if self.is_template_parameter() {
            return true;
        }

        let mut found_template_parameter = false;
        self.visit(|next| visitor(&mut found_template_parameter, next));

        found_template_parameter
    }

    /// Is this cursor pointing a valid referent?
    fn is_valid(&self) -> bool {
        self.kind().is_valid()
    }

    /// Get the source location for the referent.
    fn location(&self) -> Option<SourceLocation<'tu>> {
        self.entity().get_location()
    }

    /// Get the source location range for the referent.
    fn extent(&self) -> Option<clang::source::SourceRange<'tu>> {
        self.entity().get_range()
    }

    /// Get the raw declaration comment for this referent, if one exists.
    fn raw_comment(&self) -> Option<String> {
        self.entity().get_comment()
    }

    /// Get the referent's parsed comment.
    fn comment(&self) -> Option<Comment<'tu>> {
        self.entity().get_parsed_comment()
    }

    /// Get the referent's type.
    fn cur_type(&self) -> Option<Type<'tu>> {
        self.entity().get_type()
    }

    /// Given that this cursor's referent is a reference to another type, or is
    /// a declaration, get the cursor pointing to the referenced type or type of
    /// the declared thing.
    fn definition(&self) -> Option<Cursor> {
        self.entity().get_definition()
    }

    /// Given that this cursor's referent is reference type, get the cursor
    /// pointing to the referenced type.
    fn referenced(&self) -> Option<Cursor> {
        self.entity().get_reference()
    }

    /// Get the canonical cursor for this referent.
    ///
    /// Many types can be declared multiple times before finally being properly
    /// defined. This method allows us to get the canonical cursor for the
    /// referent type.
    fn canonical(&self) -> Cursor {
        self.entity().get_canonical_entity()
    }

    /// Given that this cursor points to either a template specialization or a
    /// template instantiation, get a cursor pointing to the template definition
    /// that is being specialized.
    fn specialized(&self) -> Option<Cursor> {
        self.entity().get_template()
    }

    /// Assuming that this cursor's referent is a template declaration, get the
    /// kind of cursor that would be generated for its specializations.
    fn template_kind(&self) -> Option<EntityKind> {
        self.entity().get_template_kind()
    }

    /// Traverse this cursor's referent and its children.
    ///
    /// Call the given function on each AST node traversed.
    fn visit<Visitor>(&self, mut visitor: Visitor)
    where
        Visitor: FnMut(Cursor) -> clang::EntityVisitResult,
    {
        self.entity()
            .visit_children(|entity, _parent| visitor(entity));
    }

    /// Collect all of this cursor's children into a vec and return them.
    fn collect_children(&self) -> Vec<Cursor> {
        let mut children = vec![];
        self.visit(|c| {
            children.push(c);
            clang::EntityVisitResult::Continue
        });
        children
    }

    /// Does this cursor have any children?
    fn has_children(&self) -> bool {
        let mut has_children = false;
        self.visit(|_| {
            has_children = true;
            clang::EntityVisitResult::Break
        });
        has_children
    }

    /// Does this cursor have at least `n` children?
    fn has_at_least_num_children(&self, n: usize) -> bool {
        assert!(n > 0);
        let mut num_left = n;
        self.visit(|_| {
            num_left -= 1;
            if num_left == 0 {
                clang::EntityVisitResult::Break
            } else {
                clang::EntityVisitResult::Continue
            }
        });
        num_left == 0
    }

    /// Returns whether the given location contains a cursor with the given
    /// kind in the first level of nesting underneath (doesn't look
    /// recursively).
    fn contains_cursor(&self, kind: EntityKind) -> bool {
        let mut found = false;

        self.visit(|c| {
            if c.kind() == kind {
                found = true;
                clang::EntityVisitResult::Break
            } else {
                clang::EntityVisitResult::Continue
            }
        });

        found
    }

    /// Is the referent an inlined function?
    fn is_inlined_function(&self) -> bool {
        self.entity().is_inline_function()
    }

    /// Is the referent a defaulted function?
    fn is_defaulted_function(&self) -> bool {
        self.entity().is_defaulted()
    }

    /// Is the referent a deleted function?
    fn is_deleted_function(&self) -> bool {
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
    fn is_bit_field(&self) -> bool {
        self.entity().is_bit_field()
    }

    /// Get a cursor to the bit field's width expression, or `None` if it's not
    /// a bit field.
    fn bit_width_expr(&self) -> Option<Cursor> {
        if !self.is_bit_field() {
            return None;
        }

        let mut result = None;
        self.visit(|cur| {
            // The first child may or may not be a TypeRef, depending on whether
            // the field's type is builtin. Skip it.
            if cur.kind() == EntityKind::TypeRef {
                return clang::EntityVisitResult::Continue;
            }

            // The next expression or literal is the bit width.
            result = Some(cur);

            clang::EntityVisitResult::Break
        });

        result
    }

    /// Get the width of this cursor's referent bit field, or `None` if the
    /// referent is not a bit field or if the width could not be evaluated.
    fn bit_width(&self) -> Option<usize> {
        // It is not safe to check the bit width without ensuring it doesn't
        // depend on a template parameter. See
        // https://github.com/rust-lang/rust-bindgen/issues/2239
        if self.bit_width_expr()?.is_dependent_on_template_parameter() {
            return None;
        }

        self.entity().get_bit_field_width()
    }

    /// Get the integer representation type used to hold this cursor's referent
    /// enum type.
    fn enum_type(&self) -> Option<Type<'tu>> {
        self.entity().get_enum_underlying_type()
    }

    /// Get the boolean constant value for this cursor's enum variant referent.
    ///
    /// Returns None if the cursor's referent is not an enum variant.
    fn enum_val_boolean(&self) -> Option<bool> {
        self.entity()
            .get_enum_constant_value()
            .map(|(signed, _unsigned)| signed != 0)
    }

    /// Get the signed constant value for this cursor's enum variant referent.
    ///
    /// Returns None if the cursor's referent is not an enum variant.
    fn enum_val_signed(&self) -> Option<i64> {
        self.entity()
            .get_enum_constant_value()
            .map(|(signed, _unsigned)| signed)
    }

    /// Get the unsigned constant value for this cursor's enum variant referent.
    ///
    /// Returns None if the cursor's referent is not an enum variant.
    fn enum_val_unsigned(&self) -> Option<u64> {
        self.entity()
            .get_enum_constant_value()
            .map(|(_signed, unsigned)| unsigned)
    }

    /// Does this cursor have the given attributes?
    fn has_attrs<const N: usize>(&self, attrs: &[Attribute; N]) -> [bool; N] {
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
                                t.get_kind() == attr.token_kind &&
                                    t.get_spelling() == attr.name
                            }))
                    {
                        *found_attr = true;
                        found_count += 1;

                        if found_count == N {
                            return clang::EntityVisitResult::Break;
                        }
                    }
                }
            }

            clang::EntityVisitResult::Continue
        });

        found_attrs
    }

    /// Given that this cursor's referent is a `typedef`, get the `Type` that is
    /// being aliased.
    fn typedef_type(&self) -> Option<Type<'tu>> {
        self.entity().get_typedef_underlying_type()
    }

    /// Get the linkage kind for this cursor's referent.
    ///
    /// This only applies to functions and variables.
    fn linkage(&self) -> Option<clang::Linkage> {
        self.entity().get_linkage()
    }

    /// Get the visibility of this cursor's referent.
    fn visibility(&self) -> Option<clang::Visibility> {
        self.entity().get_visibility()
    }

    /// Given that this cursor's referent is a function, return cursors to its
    /// parameters.
    ///
    /// Returns None if the cursor's referent is not a function/method call or
    /// declaration.
    fn args(&self) -> Option<Vec<Cursor>> {
        self.entity().get_arguments()
    }

    /// Given that this cursor's referent is a function/method call or
    /// declaration, return the number of arguments it takes.
    ///
    /// Returns Err if the cursor's referent is not a function/method call or
    /// declaration.
    fn num_args(&self) -> Option<usize> {
        self.entity().get_arguments().map(|args| args.len())
    }

    /// Get the access specifier for this cursor's referent.
    fn access_specifier(&self) -> Option<clang::Accessibility> {
        self.entity().get_accessibility()
    }

    /// Is the cursor's referrent publically accessible in C++?
    ///
    /// Returns true if self.access_specifier() is `CX_CXXPublic` or
    /// `CX_CXXInvalidAccessSpecifier`.
    fn public_accessible(&self) -> bool {
        let access = self.access_specifier();
        matches!(Some(clang::Accessibility::Public), access)
    }

    /// Is this cursor's referent a field declaration that is marked as
    /// `mutable`?
    fn is_mutable_field(&self) -> bool {
        self.entity().is_mutable()
    }

    /// Get the offset of the field represented by the Cursor.
    fn offset_of_field(&self) -> Result<usize, LayoutError> {
        self.entity().get_offset_of_field().map_err(From::from)
    }

    /// Is this cursor's referent a member function that is declared `static`?
    fn method_is_static(&self) -> bool {
        self.entity().is_static_method()
    }

    /// Is this cursor's referent a member function that is declared `const`?
    fn method_is_const(&self) -> bool {
        self.entity().is_const_method()
    }

    /// Is this cursor's referent a member function that is virtual?
    fn method_is_virtual(&self) -> bool {
        self.entity().is_virtual_method()
    }

    /// Is this cursor's referent a member function that is pure virtual?
    fn method_is_pure_virtual(&self) -> bool {
        self.entity().is_pure_virtual_method()
    }

    /// Is this cursor's referent a struct or class with virtual members?
    fn is_virtual_base(&self) -> bool {
        self.entity().is_virtual_base()
    }

    /// Try to evaluate this cursor.
    fn evaluate(&self) -> Option<EvalResult> {
        EvalResult::new(self.entity())
    }

    /// Return the result type for this cursor
    fn ret_type(&self) -> Option<Type> {
        self.entity().get_result_type()
    }

    /// Gets the tokens that correspond to that cursor.
    fn tokens(&self) -> Vec<clang::token::Token<'tu>> {
        self.entity()
            .get_range()
            .map(|range| range.tokenize())
            .unwrap_or_default()
    }

    /// Gets the tokens that correspond to that cursor as  `cexpr` tokens.
    fn cexpr_tokens(&self) -> Vec<cexpr::token::Token> {
        self.tokens()
            .into_iter()
            .filter_map(|token| token.as_cexpr_token())
            .collect()
    }

    /// Obtain the real path name of a cursor of InclusionDirective kind.
    ///
    /// Returns None if the cursor does not include a file, otherwise the file's full name
    fn get_included_file_name(&self) -> Option<PathBuf> {
        self.entity().get_file().map(|file| file.get_path())
    }
}

/// A cursor into the Clang AST, pointing to an AST node.
///
/// We call the AST node pointed to by the cursor the cursor's "referent".
pub(crate) type Cursor<'tu> = Entity<'tu>;

impl<'tu> EntityExt<'tu> for Cursor<'tu> {
    fn entity(self) -> Entity<'tu> {
        self
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

impl From<clang::SizeofError> for LayoutError {
    fn from(err: clang::SizeofError) -> Self {
        match err {
            clang::SizeofError::Dependent => Self::Dependent,
            clang::SizeofError::Incomplete => Self::Incomplete,
            clang::SizeofError::VariableSize => Self::NotConstantSize,
            clang::SizeofError::InvalidFieldName => Self::InvalidFieldName,
        }
    }
}

impl From<clang::AlignofError> for LayoutError {
    fn from(err: clang::AlignofError) -> Self {
        match err {
            clang::AlignofError::Dependent => Self::Dependent,
            clang::AlignofError::Incomplete => Self::Incomplete,
        }
    }
}

impl From<clang::OffsetofError> for LayoutError {
    fn from(err: clang::OffsetofError) -> Self {
        match err {
            clang::OffsetofError::Dependent => Self::Dependent,
            clang::OffsetofError::Incomplete => Self::Incomplete,
            clang::OffsetofError::Name => Self::Unknown,
            clang::OffsetofError::Parent => Self::Unknown,
            clang::OffsetofError::Undeduced => Self::Unknown,
        }
    }
}

pub(crate) trait TypeExt<'tu> {
    fn ty(&self) -> Type<'tu>;

    /// Get this type's kind.
    fn kind(&self) -> clang::TypeKind {
        self.ty().get_kind()
    }

    /// Get a cursor pointing to this type's declaration.
    fn declaration(&self) -> Option<Cursor<'tu>> {
        self.ty().get_declaration()
    }

    /// Get the canonical declaration of this type, if it is available.
    fn canonical_declaration(
        &self,
        location: Option<Cursor<'tu>>,
    ) -> Option<CanonicalTypeDeclaration> {
        let mut declaration = self.declaration();
        if let Some(declaration) = declaration {
            if !declaration.is_valid() {
                if let Some(mut location) = location {
                    if let Some(referenced) = location.referenced() {
                        location = referenced;
                    }
                    if location.is_template_like() {
                        declaration = location;
                    }
                }
            }
            let canonical = declaration.canonical();
            if canonical.is_valid() {
                Some(CanonicalTypeDeclaration(self.ty(), canonical))
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Get a raw display name for this type.
    fn spelling(&self) -> String {
        let s = self.ty().get_display_name();
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
    fn is_const(&self) -> bool {
        self.ty().is_const_qualified()
    }

    #[inline]
    fn is_non_deductible_auto_type(&self) -> bool {
        debug_assert_eq!(self.kind(), clang::TypeKind::Auto);
        self.canonical_type() == self.ty()
    }

    /// What is the size of this type? Paper over invalid types by returning `0`
    /// for them.
    fn size(&self, ctx: &BindgenContext) -> usize {
        self.fallible_size(ctx).unwrap_or_default()
    }

    /// What is the size of this type?
    fn fallible_size(
        &self,
        ctx: &BindgenContext,
    ) -> Result<usize, LayoutError> {
        match self.kind() {
            // Work-around https://bugs.llvm.org/show_bug.cgi?id=40975
            clang::TypeKind::RValueReference |
            clang::TypeKind::LValueReference => Ok(ctx.target_pointer_size()),
            // Work-around https://bugs.llvm.org/show_bug.cgi?id=40813
            clang::TypeKind::Auto if self.is_non_deductible_auto_type() => {
                Err(LayoutError::Unknown)
            }
            _ => Ok(self.ty().get_sizeof()?),
        }
    }

    /// What is the alignment of this type? Paper over invalid types by
    /// returning `0`.
    fn align(&self, ctx: &BindgenContext) -> usize {
        self.fallible_align(ctx).unwrap_or_default()
    }

    /// What is the alignment of this type?
    fn fallible_align(
        &self,
        ctx: &BindgenContext,
    ) -> Result<usize, LayoutError> {
        match self.kind() {
            // Work-around https://bugs.llvm.org/show_bug.cgi?id=40975
            clang::TypeKind::RValueReference |
            clang::TypeKind::LValueReference => Ok(ctx.target_pointer_size()),
            // Work-around https://bugs.llvm.org/show_bug.cgi?id=40813
            clang::TypeKind::Auto if self.is_non_deductible_auto_type() => {
                Err(LayoutError::Unknown)
            }
            _ => Ok(self.ty().get_alignof()?),
        }
    }

    /// Get the layout for this type, or an error describing why it does not
    /// have a valid layout.
    fn fallible_layout(
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
    fn num_template_args(&self) -> Option<usize> {
        self.ty()
            .get_template_argument_types()
            .map(|args| args.len())
    }

    /// If this type is a class template specialization, return its
    /// template arguments. Otherwise, return None.
    fn template_args(&self) -> Option<Vec<Option<Type<'tu>>>> {
        self.ty().get_template_argument_types()
    }

    /// Given that this type is a function prototype, return the types of its parameters.
    ///
    /// Returns None if the type is not a function prototype.
    fn args(&self) -> Option<Vec<Type<'tu>>> {
        self.ty().get_argument_types()
    }

    /// Given that this type is a function prototype, return the number of arguments it takes.
    ///
    /// Returns Err if the type is not a function prototype.
    fn num_args(&self) -> Option<usize> {
        self.ty().get_argument_types().map(|args| args.len())
    }

    /// Given that this type is a pointer type, return the type that it points
    /// to.
    fn pointee_type(&self) -> Option<Type<'tu>> {
        match self.kind() {
            clang::TypeKind::Pointer |
            clang::TypeKind::RValueReference |
            clang::TypeKind::LValueReference |
            clang::TypeKind::MemberPointer |
            clang::TypeKind::BlockPointer |
            clang::TypeKind::ObjCObjectPointer => self.ty().get_pointee_type(),
            _ => None,
        }
    }

    /// Given that this type is an array, vector, or complex type, return the
    /// type of its elements.
    fn elem_type(&self) -> Option<Type<'tu>> {
        self.ty().get_element_type()
    }

    /// Given that this type is an array or vector type, return its number of
    /// elements.
    fn num_elements(&self) -> Option<usize> {
        self.ty().get_size()
    }

    /// Get the canonical version of this type. This sees through `typedef`s and
    /// aliases to get the underlying, canonical type.
    fn canonical_type(&self) -> Type<'tu> {
        self.ty().get_canonical_type()
    }

    /// Is this type a variadic function type?
    fn is_variadic(&self) -> bool {
        self.ty().is_variadic()
    }

    /// Given that this type is a function type, get the type of its return
    /// value.
    fn ret_type(&self) -> Option<Type<'tu>> {
        self.ty().get_result_type()
    }

    /// Given that this type is a function type, get its calling convention. If
    /// this is not a function type, `CXCallingConv_Invalid` is returned.
    fn call_conv(&self) -> Option<clang::CallingConvention> {
        self.ty().get_calling_convention()
    }

    /// For elaborated types (types which use `class`, `struct`, or `union` to
    /// disambiguate types from local bindings), get the underlying type.
    fn named(&self) -> Option<Type<'tu>> {
        self.ty().get_elaborated_type()
    }

    /// Is this a valid and exposed type?
    fn is_valid_and_exposed(&self) -> bool {
        self.kind() != clang::TypeKind::Unexposed
    }

    /// Is this type a fully instantiated template?
    fn is_fully_instantiated_template(&self) -> bool {
        // Yep, the spelling of this containing type-parameter is extremely
        // nasty... But can happen in <type_traits>. Unfortunately I couldn't
        // reduce it enough :(
        self.template_args().map_or(false, |args| args.len() > 0) &&
            !matches!(
                self.declaration().unwrap().kind(),
                clang::EntityKind::ClassTemplatePartialSpecialization |
                    clang::EntityKind::TypeAliasTemplateDecl |
                    clang::EntityKind::TemplateTemplateParameter
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
    fn is_associated_type(&self) -> bool {
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

impl<'tu> TypeExt<'tu> for Type<'tu> {
    fn ty(&self) -> Type<'tu> {
        *self
    }
}

/// The `CanonicalTypeDeclaration` type exists as proof-by-construction that its
/// cursor is the canonical declaration for its type. If you have a
/// `CanonicalTypeDeclaration` instance, you know for sure that the type and
/// cursor match up in a canonical declaration relationship, and it simply
/// cannot be otherwise.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CanonicalTypeDeclaration<'tu>(Type<'tu>, Cursor<'tu>);

impl<'tu> CanonicalTypeDeclaration<'tu> {
    /// Get the type.
    pub(crate) fn ty(&self) -> Type<'tu> {
        self.0
    }

    /// Get the type's canonical declaration cursor.
    pub(crate) fn cursor(&self) -> Cursor<'tu> {
        self.1
    }
}
pub(crate) trait SourceLocationExt<'tu> {
    fn source_location(&self) -> SourceLocation<'tu>;

    /// Get the (file, line, column, byte offset) tuple for this source
    /// location.
    fn location(&self) -> (Option<File<'tu>>, usize, usize, usize) {
        let location = self.source_location().get_file_location();
        (
            location.file,
            location.line as usize,
            location.column as usize,
            location.offset as usize,
        )
    }
}
impl<'tu> SourceLocationExt<'tu> for SourceLocation<'tu> {
    fn source_location(&self) -> SourceLocation<'tu> {
        *self
    }
}

trait CommentExt<'tu> {
    fn comment(&self) -> Comment<'tu>;

    /// Get this comment's children comment
    fn get_children(&self) -> Vec<clang::documentation::CommentChild> {
        self.comment().get_children()
    }
}

impl<'tu> CommentExt<'tu> for Comment<'tu> {
    fn comment(&self) -> Comment<'tu> {
        *self
    }
}

pub(crate) trait FileExt<'tu> {
    fn file(&self) -> File<'tu>;
    /// Get the name of this source file.
    fn name(&self) -> String {
        self.file().get_path().display().to_string()
    }
}

impl<'tu> FileExt<'tu> for File<'tu> {
    fn file(&self) -> File<'tu> {
        *self
    }
}

pub(crate) trait TranslationUnitExt<'i> {
    fn translation_unit(&self) -> TranslationUnit<'i>;

    /// Parse a source file into a translation unit.
    fn parse<'c, P: Into<PathBuf>>(
        ix: &Index<'c>,
        file: P,
        cmd_args: &[String],
        unsaved: &[UnsavedFile],
        detailed_preprocessing_record: bool,
    ) -> Result<TranslationUnit<'i>, clang::SourceError> {
        ix.parser(file)
            .detailed_preprocessing_record(detailed_preprocessing_record)
            .arguments(cmd_args)
            .unsaved(unsaved)
            .parse()
    }

    /// Get the Clang diagnostic information associated with this translation
    /// unit.
    fn diags(&self) -> Vec<Diagnostic<'i>> {
        self.translation_unit().get_diagnostics()
    }

    /// Get a cursor pointing to the root of this translation unit's AST.
    fn cursor(&self) -> Cursor {
        self.translation_unit().get_entity()
    }
}

impl<'i> TranslationUnitExt<'i> for TranslationUnit<'i> {
    fn translation_unit(&self) -> TranslationUnit<'i> {
        *self
    }
}

pub(crate) type UnsavedFile = clang::Unsaved;

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

/// Convert a cursor kind into a static string.
pub(crate) fn kind_to_str(kind: EntityKind) -> String {
    unsafe { cxstring_into_string(clang_getCursorKindSpelling(kind as _)) }
}

/// Convert a type kind to a static string.
pub(crate) fn type_to_str(kind: TypeKind) -> String {
    unsafe { cxstring_into_string(clang_getTypeKindSpelling(kind as _)) }
}

/// Dump the Clang AST to stdout for debugging purposes.
pub(crate) fn ast_dump(
    c: Cursor<'_>,
    depth: isize,
) -> clang::EntityVisitResult {
    fn print_indent<S: AsRef<str>>(depth: isize, s: S) {
        for _ in 0..depth {
            print!("    ");
        }
        println!("{}", s.as_ref());
    }

    fn print_cursor<S: AsRef<str>>(depth: isize, prefix: S, c: Cursor<'_>) {
        let prefix = prefix.as_ref();
        print_indent(
            depth,
            format!(" {}kind = {}", prefix, kind_to_str(c.kind())),
        );
        print_indent(
            depth,
            format!(" {}spelling = \"{}\"", prefix, c.spelling()),
        );
        print_indent(
            depth,
            format!(" {}location = {:?}", prefix, c.location()),
        );
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

        if let Some(templ_kind) = c.template_kind() {
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
        if let Some(num) = c.num_args() {
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
            if refd != c {
                println!();
                print_cursor(depth, String::from(prefix) + "referenced.", refd);
            }
        }

        let canonical = c.canonical();
        if canonical != c {
            println!();
            print_cursor(depth, String::from(prefix) + "canonical.", canonical);
        }

        if let Some(specialized) = c.specialized() {
            if specialized != c {
                println!();
                print_cursor(
                    depth,
                    String::from(prefix) + "specialized.",
                    specialized,
                );
            }
        }

        if let Some(parent) = c.fallible_semantic_parent() {
            println!();
            print_cursor(
                depth,
                String::from(prefix) + "semantic-parent.",
                parent,
            );
        }
    }

    fn print_type<S: AsRef<str>>(depth: isize, prefix: S, ty: Type<'_>) {
        let prefix = prefix.as_ref();

        let kind = ty.kind();
        print_indent(depth, format!(" {}kind = {}", prefix, type_to_str(kind)));

        print_indent(depth, format!(" {}cconv = {:?}", prefix, ty.call_conv()));

        print_indent(
            depth,
            format!(" {}spelling = \"{}\"", prefix, ty.spelling()),
        );

        if let Some(num_template_args) = ty.num_template_args() {
            if num_template_args >= 0 {
                print_indent(
                    depth,
                    format!(
                        " {}number-of-template-args = {}",
                        prefix, num_template_args
                    ),
                );
            }
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
        if canonical != ty {
            println!();
            print_type(depth, String::from(prefix) + "canonical.", canonical);
        }

        if let Some(pointee) = ty.pointee_type() {
            if pointee != ty {
                println!();
                print_type(depth, String::from(prefix) + "pointee.", pointee);
            }
        }

        if let Some(elem) = ty.elem_type() {
            if elem != ty {
                println!();
                print_type(depth, String::from(prefix) + "elements.", elem);
            }
        }

        if let Some(ret) = ty.ret_type() {
            if ret != ty {
                println!();
                print_type(depth, String::from(prefix) + "return.", ret);
            }
        }

        if let Some(named) = ty.named() {
            if named != ty {
                println!();
                print_type(depth, String::from(prefix) + "named.", named);
            }
        }
    }

    print_indent(depth, "(");
    print_cursor(depth, "", c);

    println!();
    if let Some(ty) = c.cur_type() {
        print_type(depth, "type.", ty);

        if let Some(declaration) = ty.declaration() {
            if declaration != c {
                println!();
                print_cursor(depth, "type.declaration.", declaration);
            }
        }
    }

    // Recurse.
    let mut found_children = false;
    c.visit(|s| {
        if !found_children {
            println!();
            found_children = true;
        }
        ast_dump(s, depth + 1)
    });

    print_indent(depth, ")");

    clang::EntityVisitResult::Continue
}

/// Try to extract the clang version to a string
pub(crate) fn extract_clang_version() -> String {
    clang::get_version()
}

/// A wrapper for the result of evaluating an expression.
#[derive(Debug)]
pub(crate) struct EvalResult<'tu> {
    x: clang::EvaluationResult,
    ty: Type<'tu>,
}

impl<'tu> EvalResult<'tu> {
    /// Evaluate `cursor` and return the result.
    pub(crate) fn new(cursor: Cursor<'tu>) -> Option<Self> {
        // Work around https://bugs.llvm.org/show_bug.cgi?id=42532, see:
        //  * https://github.com/rust-lang/rust-bindgen/issues/283
        //  * https://github.com/rust-lang/rust-bindgen/issues/1590
        {
            let mut found_cant_eval = false;
            cursor.visit(|c| {
                if c.kind() == EntityKind::TypeRef &&
                    c.cur_type().map(|ty| ty.canonical_type().kind()) ==
                        Some(clang::TypeKind::Unexposed)
                {
                    found_cant_eval = true;
                    return clang::EntityVisitResult::Break;
                }

                clang::EntityVisitResult::Recurse
            });

            if found_cant_eval {
                return None;
            }
        }
        Some(EvalResult {
            x: cursor.evaluate()?,
            ty: cursor.cur_type()?.canonical_type(),
        })
    }

    /// Try to get back the result as a double.
    fn as_double(&self) -> Option<f64> {
        match self.x {
            clang::EvaluationResult::Float(float) => Some(float),
            _ => None,
        }
    }

    /// Try to get back the result as an integer.
    fn as_int(&self) -> Option<i64> {
        match self.x {
            clang::EvaluationResult::SignedInteger(int) => Some(int),
            _ => None,
        }
    }

    /// Evaluates the expression as a literal string, that may or may not be
    /// valid utf-8.
    fn as_literal_string(&self) -> Option<Vec<u8>> {
        match self.x {
            clang::EvaluationResult::String(str) => {
                let char_ty =
                    self.ty.pointee_type().or_else(|| self.ty.elem_type())?;
                match char_ty.kind() {
                    clang::TypeKind::CharS |
                    clang::TypeKind::SChar |
                    clang::TypeKind::CharU |
                    clang::TypeKind::UChar => Some(str.to_bytes().to_owned()),
                    // FIXME: Support generating these.
                    clang::TypeKind::Char16 => None,
                    clang::TypeKind::Char32 => None,
                    clang::TypeKind::WChar => None,
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

trait TokenExt<'tu> {
    /// Converts a ClangToken to a `cexpr` token if possible.
    fn as_cexpr_token(&self) -> Option<cexpr::token::Token>;
}

impl<'tu> TokenExt<'tu> for clang::token::Token<'tu> {
    fn as_cexpr_token(&self) -> Option<cexpr::token::Token> {
        use cexpr::token;

        let kind = match self.get_kind() {
            TokenKind::Punctuation => token::Kind::Punctuation,
            TokenKind::Literal => token::Kind::Literal,
            TokenKind::Identifier => token::Kind::Identifier,
            TokenKind::Keyword => token::Kind::Keyword,
            // NB: cexpr is not too happy about comments inside
            // expressions, so we strip them down here.
            TokenKind::Comment => return None,
            _ => {
                warn!("Found unexpected token kind: {:?}", self);
                return None;
            }
        };

        Some(token::Token {
            kind,
            raw: self.get_spelling().into_bytes().into_boxed_slice(),
        })
    }
}

pub(crate) type TargetInfo = clang::Target;
