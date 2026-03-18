use oxc_span::CompactStr;

/// A compile-time constant value from a TypeScript enum member.
/// Per the TypeScript spec, enum members can only evaluate to numbers or strings.
#[derive(Debug, Clone, PartialEq)]
pub enum ConstantValue {
    Number(f64),
    String(CompactStr),
}
