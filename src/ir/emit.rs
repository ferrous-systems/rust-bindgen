use std::fmt::{self, Write};

use crate::callbacks::IntKind;

use super::context::{BindgenContext, TypeId};
use super::function::{Function, FunctionKind};
use super::ty::{FloatKind, TypeKind};

#[derive(Debug)]
pub(crate) struct CItem {
    header: String,
    code: String,
}

impl CItem {
    pub(crate) fn from_function(
        function: &Function,
        ctx: &BindgenContext,
    ) -> Self {
        match function.kind() {
            FunctionKind::Function => {
                let signature_type = ctx.resolve_type(function.signature());
                match signature_type.kind() {
                    TypeKind::Function(signature) => {
                        let mut buf = String::new();

                        let mut count = 0;

                        let name = function.name();
                        let args = signature
                            .argument_types()
                            .iter()
                            .cloned()
                            .map(|(opt_name, type_id)| {
                                (
                                    opt_name.unwrap_or_else(|| {
                                        let name = format!("arg_{}", count);
                                        count += 1;
                                        name
                                    }),
                                    type_id,
                                )
                            })
                            .collect::<Vec<_>>();

                        emit_type(signature.return_type(), ctx, &mut buf)
                            .unwrap();
                        write!(buf, " {}__extern(", name).unwrap();
                        emit_sep(
                            ", ",
                            args.iter(),
                            ctx,
                            &mut buf,
                            |(name, type_id), ctx, buf| {
                                emit_type(*type_id, ctx, buf)?;
                                write!(buf, " {}", name)
                            },
                        )
                        .unwrap();
                        write!(buf, ")").unwrap();

                        let header = format!("{};", buf);

                        write!(buf, " {{ return {}(", name).unwrap();
                        emit_sep(
                            ", ",
                            args.iter(),
                            ctx,
                            &mut buf,
                            |(name, _), _, buf| write!(buf, "{}", name),
                        )
                        .unwrap();
                        write!(buf, "); }}").unwrap();

                        Self { header, code: buf }
                    }
                    _ => unreachable!(),
                }
            }
            FunctionKind::Method(_) => todo!(),
        }
    }

    pub(crate) fn header(&self) -> &str {
        self.header.as_ref()
    }

    pub(crate) fn code(&self) -> &str {
        self.code.as_ref()
    }
}

fn emit_sep<
    W: fmt::Write,
    F: Fn(I::Item, &BindgenContext, &mut W) -> fmt::Result,
    I: Iterator,
>(
    sep: &'static str,
    mut iter: I,
    ctx: &BindgenContext,
    buf: &mut W,
    f: F,
) -> fmt::Result {
    if let Some(item) = iter.next() {
        f(item, ctx, buf)?;

        for item in iter {
            write!(buf, "{}", sep)?;
            f(item, ctx, buf)?;
        }
    }

    Ok(())
}

fn emit_type<W: fmt::Write>(
    type_id: TypeId,
    ctx: &BindgenContext,
    buf: &mut W,
) -> fmt::Result {
    match ctx.resolve_type(type_id).kind() {
        TypeKind::Void => write!(buf, "void"),
        TypeKind::NullPtr => write!(buf, "nullptr_t"),
        TypeKind::Int(int_kind) => match int_kind {
            IntKind::Bool => write!(buf, "bool"),
            IntKind::SChar => write!(buf, "signed char"),
            IntKind::UChar => write!(buf, "unsigned char"),
            IntKind::WChar => write!(buf, "wchar_t"),
            IntKind::Short => write!(buf, "short"),
            IntKind::UShort => write!(buf, "unsigned short"),
            IntKind::Int => write!(buf, "int"),
            IntKind::UInt => write!(buf, "unsigned int"),
            IntKind::Long => write!(buf, "long"),
            IntKind::ULong => write!(buf, "unsigned long"),
            IntKind::LongLong => write!(buf, "long long"),
            IntKind::ULongLong => write!(buf, "unsigned long long"),
            _ => todo!(),
        },
        TypeKind::Float(float_kind) => match float_kind {
            FloatKind::Float => write!(buf, "float"),
            FloatKind::Double => write!(buf, "double"),
            FloatKind::LongDouble => write!(buf, "long double"),
            FloatKind::Float128 => write!(buf, "__float128"),
        },
        TypeKind::Complex(float_kind) => match float_kind {
            FloatKind::Float => write!(buf, "float complex"),
            FloatKind::Double => write!(buf, "double complex"),
            FloatKind::LongDouble => write!(buf, "long double complex"),
            FloatKind::Float128 => write!(buf, "__complex128"),
        },
        TypeKind::Alias(type_id) => emit_type(*type_id, ctx, buf),
        TypeKind::TemplateAlias(type_id, params) => {
            emit_type(*type_id, ctx, buf)?;
            write!(buf, "<")?;
            emit_sep(", ", params.iter().copied(), ctx, buf, emit_type)?;
            write!(buf, ">")
        }
        TypeKind::Array(type_id, length) => {
            emit_type(*type_id, ctx, buf)?;
            write!(buf, " [{}]", length)
        }
        TypeKind::Function(signature) => {
            emit_type(signature.return_type(), ctx, buf)?;
            write!(buf, " (")?;
            emit_sep(
                ", ",
                signature.argument_types().iter(),
                ctx,
                buf,
                |(name, type_id), ctx, buf| {
                    emit_type(*type_id, ctx, buf)?;

                    if let Some(name) = name {
                        write!(buf, "{}", name)?;
                    }

                    Ok(())
                },
            )?;
            write!(buf, ")")
        }
        TypeKind::ResolvedTypeRef(type_id) => emit_type(*type_id, ctx, buf),
        t => todo!("{:?}", t),
    }
}
