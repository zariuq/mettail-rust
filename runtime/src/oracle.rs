//! Language-agnostic oracle query contract.
//!
//! This gives runtimes a principled way to expose external/FFI-style services
//! through a typed query surface, without coupling to a specific language.

/// Descriptor for a language-exposed oracle endpoint.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OracleDescriptor {
    pub name: String,
    pub operations: Vec<String>,
    pub docs: Option<String>,
}

impl OracleDescriptor {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            operations: Vec::new(),
            docs: None,
        }
    }
}

/// One oracle invocation request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OracleQuery {
    pub oracle: String,
    pub operation: String,
    pub args: Vec<String>,
}

impl OracleQuery {
    pub fn new(oracle: impl Into<String>, operation: impl Into<String>, args: Vec<String>) -> Self {
        Self {
            oracle: oracle.into(),
            operation: operation.into(),
            args,
        }
    }
}

/// A textual row-oriented response so REPL/CLI consumers can inspect results
/// without language-specific decoding.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct OracleResponse {
    pub rows: Vec<Vec<String>>,
    pub diagnostics: Vec<String>,
}
