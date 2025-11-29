use proc_macro2::Span;

use crate::create_syn_error;
use crate::generation::common::PANIC_ERROR_MESSAGE;
use crate::parsing::types::IntegerType::{
    Bool, I8, I16, I32, I64, I128, Isize, U8, U16, U32, U64, U128, Usize,
};

#[derive(Debug)]
#[derive_const(PartialEq, Eq)]
pub(crate) enum IntegerType {
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
    Bool,
    UnknownInteger,
}

impl IntegerType {
    pub fn parse_from_syn_ident(i: &syn::Ident) -> Self {
        Self::from_str(i.to_string().as_str())
    }
    pub fn from_str(s: &str) -> Self {
        match s {
            "u8" => Self::U8,
            "u16" => Self::U16,
            "u32" => Self::U32,
            "u64" => Self::U64,
            "u128" => Self::U128,
            "usize" => Self::Usize,
            "i8" => Self::I8,
            "i16" => Self::I16,
            "i32" => Self::I32,
            "i64" => Self::I64,
            "i128" => Self::I128,
            "isize" => Self::Isize,
            "bool" => Self::Bool,
            _ => Self::UnknownInteger,
        }
    }
    pub fn parse_from_syn_type(ty: &syn::Type) -> Self {
        get_type_ident(ty).as_deref().map(Self::from_str).unwrap_or(Self::UnknownInteger)
    }
    pub fn get_integer_suffix(&self) -> syn::Result<&'static str> {
        match self {
            U8 => Ok("u8"),
            U16 => Ok("u16"),
            U32 => Ok("u32"),
            U64 => Ok("u64"),
            U128 => Ok("u128"),
            Usize => Ok("usize"),
            I8 => Ok("i8"),
            I16 => Ok("i16"),
            I32 => Ok("i32"),
            I64 => Ok("i64"),
            I128 => Ok("i128"),
            Isize => Ok("isize"),
            Bool => Ok("bool"),
            _ => Err(create_syn_error(Span::call_site(), PANIC_ERROR_MESSAGE))?,
        }
    }
    pub const fn is_supported_bitfield_type(&self) -> bool {
        let mut i = 0;
        while i < SUPPORTED_BITFIELD_TYPES.len() {
            if SUPPORTED_BITFIELD_TYPES[i].eq(self) {
                return true;
            }
            i += 1;
        }
        false
    }
    pub fn get_bits(&self) -> syn::Result<u8> {
        match self {
            Self::U8 | Self::I8 => Ok(8),
            Self::U16 | Self::I16 => Ok(16),
            Self::U32 | Self::I32 => Ok(32),
            Self::U64 | Self::I64 => Ok(64),
            Self::U128 | Self::I128 => Ok(128),
            _ => Err(create_syn_error(Span::call_site(), PANIC_ERROR_MESSAGE)),
        }
    }
}

const UNSIGNED_INTEGER_TYPES: [IntegerType; 6] = [U8, U16, U32, U64, U128, Usize];
const SIGNED_INTEGER_TYPES: [IntegerType; 6] = [I8, I16, I32, I64, I128, Isize];
const SUPPORTED_BITFIELD_TYPES: [IntegerType; 5] = [U8, U16, U32, U64, U128];
const SUPPORTED_BITFIELD_FIELD_TYPES: [IntegerType; 13] =
    [U8, U16, U32, U64, U128, Usize, I8, I16, I32, I64, I128, Isize, Bool];
const SIZE_TYPES: [IntegerType; 2] = [Usize, Isize];

/// Returns the integer type from the type.
pub(crate) fn get_integer_type_from_type(ty: &syn::Type) -> IntegerType {
    IntegerType::parse_from_syn_type(ty)
}

/// Returns the integer suffix from the integer type.
pub(crate) fn get_integer_suffix_from_integer_type(
    integer_type: IntegerType,
) -> syn::Result<String> {
    integer_type.get_integer_suffix().map(str::to_owned)
}

/// Returns if the type is a supported bitfield type.
#[allow(unused)]
pub(crate) fn is_supported_bitfield_type(ty: &syn::Type) -> bool {
    SUPPORTED_BITFIELD_TYPES.contains(&get_integer_type_from_type(ty))
}

/// Returns if the type is a supported bitfield field type.
pub(crate) fn is_supported_field_type(ty: &syn::Type) -> bool {
    is_custom_field_type(ty)
        || SUPPORTED_BITFIELD_FIELD_TYPES.contains(&get_integer_type_from_type(ty))
}

/// Returns if the type is an unsigned integer type.
pub(crate) fn is_unsigned_integer_type(ty: &syn::Type) -> bool {
    UNSIGNED_INTEGER_TYPES.contains(&get_integer_type_from_type(ty)) || is_bool_type(ty)
}

/// Returns if the type is an unsigned integer type.
pub(crate) fn is_signed_integer_type(ty: &syn::Type) -> bool {
    SIGNED_INTEGER_TYPES.contains(&get_integer_type_from_type(ty))
}

/// Returns if the type is an unsigned integer type.
pub(crate) fn is_bool_type(ty: &syn::Type) -> bool {
    get_integer_type_from_type(ty) == Bool
}

/// Returns the number of bits of the integer type.
pub(crate) fn get_bits_from_type(ty: &syn::Type) -> syn::Result<u8> {
    #[track_caller]
    #[inline(always)]
    fn err() -> syn::Error {
        create_syn_error(Span::call_site(), PANIC_ERROR_MESSAGE)
    }
    let ident = get_type_ident(ty).ok_or_else(err)?;
    match ident.as_str() {
        "bool" => Ok(1),
        "u8" | "i8" => Ok(8),
        "u16" | "i16" => Ok(16),
        "u32" | "i32" => Ok(32),
        "u64" | "i64" => Ok(64),
        "u128" | "i128" => Ok(128),
        _ => Err(err()),
    }
}

/// Returns the number of bits of the integer type.
pub(crate) fn get_bits_from_ident(i: &syn::Ident) -> syn::Result<u8> {
    #[track_caller]
    #[inline(always)]
    fn err() -> syn::Error {
        create_syn_error(Span::call_site(), PANIC_ERROR_MESSAGE)
    }
    match i.to_string().as_str() {
        "bool" => Ok(1),
        "u8" | "i8" => Ok(8),
        "u16" | "i16" => Ok(16),
        "u32" | "i32" => Ok(32),
        "u64" | "i64" => Ok(64),
        "u128" | "i128" => Ok(128),
        _ => Err(err()),
    }
}

/// Returns if the type is a size type.
pub(crate) fn is_size_type(ty: &syn::Type) -> bool {
    SIZE_TYPES.contains(&get_integer_type_from_type(ty))
}

/// Returns if the type is a custom field type.
pub(crate) fn is_custom_field_type(ty: &syn::Type) -> bool {
    !is_unsigned_integer_type(ty) && !is_signed_integer_type(ty) && !is_bool_type(ty)
}

/// Returns the identifier of the type.
pub(crate) fn get_type_ident(ty: &syn::Type) -> Option<String> {
    if let syn::Type::Path(ty) = ty
        && let Some(segment) = ty.path.segments.first()
    {
        return Some(segment.ident.to_string());
    }

    None
}
