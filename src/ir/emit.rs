use std::io;

use crate::callbacks::IntKind;

use super::context::{BindgenContext, TypeId};
use super::function::{Function, FunctionKind};
use super::ty::{FloatKind, Type, TypeKind};

mod private {
    use super::*;

    pub trait Sealed {}

    impl Sealed for TypeId {}
    impl Sealed for (Option<String>, TypeId) {}
    impl Sealed for Type {}
    impl Sealed for Function {}
}

pub trait Emit: private::Sealed {
    fn emit<W: io::Write>(
        &self,
        ctx: &BindgenContext,
        buf: &mut W,
    ) -> io::Result<()>;
}

fn emit_sep<'a, W: io::Write, T: Emit + 'a, I: Iterator<Item = &'a T> + 'a>(
    sep: &'static str,
    mut iter: I,
    ctx: &BindgenContext,
    buf: &mut W,
) -> io::Result<()> {
    if let Some(item) = iter.next() {
        item.emit(ctx, buf)?;

        for item in iter {
            write!(buf, "{}", sep)?;
            item.emit(ctx, buf)?;
        }
    }

    Ok(())
}

impl Emit for TypeId {
    fn emit<W: io::Write>(
        &self,
        ctx: &BindgenContext,
        buf: &mut W,
    ) -> io::Result<()> {
        ctx.resolve_type(*self).emit(ctx, buf)
    }
}

impl Emit for (Option<String>, TypeId) {
    fn emit<W: io::Write>(
        &self,
        ctx: &BindgenContext,
        buf: &mut W,
    ) -> io::Result<()> {
        self.1.emit(ctx, buf)?;

        if let Some(string) = &self.0 {
            write!(buf, " {}", string)?;
        }

        Ok(())
    }
}

impl Emit for Type {
    fn emit<W: io::Write>(
        &self,
        ctx: &BindgenContext,
        buf: &mut W,
    ) -> io::Result<()> {
        match self.kind() {
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
            TypeKind::Alias(type_id) => type_id.emit(ctx, buf),
            TypeKind::TemplateAlias(type_id, params) => {
                type_id.emit(ctx, buf)?;
                write!(buf, "<")?;
                emit_sep(", ", params.iter(), ctx, buf)?;
                write!(buf, ">")
            }
            TypeKind::Array(type_id, length) => {
                type_id.emit(ctx, buf)?;
                write!(buf, " [{}]", length)
            }
            TypeKind::Function(signature) => {
                signature.return_type().emit(ctx, buf)?;
                write!(buf, " (")?;
                emit_sep(", ", signature.argument_types().iter(), ctx, buf)?;
                write!(buf, ")")
            }
            _ => todo!(),
        }
    }
}

impl Emit for Function {
    fn emit<W: io::Write>(
        &self,
        ctx: &BindgenContext,
        buf: &mut W,
    ) -> io::Result<()> {
        match self.kind() {
            FunctionKind::Function => {
                let signature_type = ctx.resolve_type(self.signature());
                match signature_type.kind() {
                    TypeKind::Function(signature) => {
                        signature.return_type().emit(ctx, buf)?;
                        write!(buf, " {}(", self.name())?;
                        emit_sep(", ", signature.argument_types().iter(), ctx, buf)?;
                        write!(buf, ")")
                    }
                    _ => unreachable!(),
                }
            }
            FunctionKind::Method(_) => todo!(),
        }
    }
}
