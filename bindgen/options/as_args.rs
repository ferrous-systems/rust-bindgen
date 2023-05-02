use std::{path::PathBuf, ffi::OsString};

use crate::RegexSet;

/// Trait used to turn [`crate::BindgenOptions`] fields into CLI args.
pub(super) trait AsArgs {
    fn as_args(&self, args: &mut Vec<OsString>, flag: &str);
}

/// If the `bool` is `true`, `flag` is pushed into `args`.
///
/// be careful about the truth value of the field as some options, like `--no-layout-tests`, are
/// actually negations of the fields.
impl AsArgs for bool {
    fn as_args(&self, args: &mut Vec<OsString>, flag: &str) {
        if *self {
            args.push(flag.into());
        }
    }
}

/// Iterate over all the items of the `RegexSet` and push `flag` followed by the item into `args`
/// for each item.
impl AsArgs for RegexSet {
    fn as_args(&self, args: &mut Vec<OsString>, flag: &str) {
        for item in self.get_items() {
            args.extend_from_slice(&[flag.into(), item.into()]);
        }
    }
}

/// If the `Option` is `Some(value)`, push `flag` followed by `value`.
impl AsArgs for Option<String> {
    fn as_args(&self, args: &mut Vec<OsString>, flag: &str) {
        if let Some(string) = self {
            args.extend_from_slice(&[flag.into(), string.into()]);
        }
    }
}

/// If the `Option` is `Some(path)`, push `flag` followed by the [`std::path::Path::display`]
/// representation of `path`.
impl AsArgs for Option<PathBuf> {
    fn as_args(&self, args: &mut Vec<OsString>, flag: &str) {
        if let Some(path) = self {
            args.extend_from_slice(&[
                flag.into(),
                path.as_os_str().to_owned(),
            ]);
        }
    }
}
