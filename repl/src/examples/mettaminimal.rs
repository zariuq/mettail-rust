// MeTTaMinimalState example terms for the REPL
//
// These are small, PeTTa-style state transition examples that fit the current
// exported MeTTaMinimal language.

use super::{Example, ExampleCategory, LanguageName};

pub fn all() -> Vec<&'static Example> {
    vec![
        &MM_EVAL_TRUE,
        &MM_EVAL_FALSE,
        &MM_RETURN_TRUE,
        &MM_RETURN_FALSE,
        &MM_DONE_NOOP,
        &MM_UNIFY_PLACEHOLDER,
        &MM_CHAIN_PLACEHOLDER,
    ]
}

pub static MM_EVAL_TRUE: Example = Example {
    name: "mm_eval_true",
    description: "One-step eval: (Eval ATrue) -> (Return ATrue)",
    source: "(State (Eval ATrue) AFalse AFalse)",
    category: ExampleCategory::Simple,
    language: LanguageName::MeTTaMinimalState,
};

pub static MM_EVAL_FALSE: Example = Example {
    name: "mm_eval_false",
    description: "One-step eval: (Eval AFalse) -> (Return AFalse)",
    source: "(State (Eval AFalse) ATrue ATrue)",
    category: ExampleCategory::Simple,
    language: LanguageName::MeTTaMinimalState,
};

pub static MM_RETURN_TRUE: Example = Example {
    name: "mm_return_true",
    description: "One-step return: (Return ATrue) -> Done",
    source: "(State (Return ATrue) AFalse AFalse)",
    category: ExampleCategory::Simple,
    language: LanguageName::MeTTaMinimalState,
};

pub static MM_RETURN_FALSE: Example = Example {
    name: "mm_return_false",
    description: "One-step return: (Return AFalse) -> Done",
    source: "(State (Return AFalse) ATrue ATrue)",
    category: ExampleCategory::Simple,
    language: LanguageName::MeTTaMinimalState,
};

pub static MM_DONE_NOOP: Example = Example {
    name: "mm_done_noop",
    description: "Terminal state: no rewrite from Done",
    source: "(State Done ATrue AFalse)",
    category: ExampleCategory::EdgeCase,
    language: LanguageName::MeTTaMinimalState,
};

pub static MM_UNIFY_PLACEHOLDER: Example = Example {
    name: "mm_unify_placeholder",
    description: "Placeholder instruction (no rewrite yet in this exported fragment)",
    source: "(State (Unify ATrue ATrue) AFalse AFalse)",
    category: ExampleCategory::EdgeCase,
    language: LanguageName::MeTTaMinimalState,
};

pub static MM_CHAIN_PLACEHOLDER: Example = Example {
    name: "mm_chain_placeholder",
    description: "Placeholder chain instruction (no rewrite yet in this exported fragment)",
    source: "(State (Chain ATrue AFalse) AFalse ATrue)",
    category: ExampleCategory::EdgeCase,
    language: LanguageName::MeTTaMinimalState,
};
