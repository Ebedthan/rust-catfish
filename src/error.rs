// Copyright 2022 Anicet Ebou.
// Licensed under the MIT license (http://opensource.org/licenses/MIT)
// This file may not be copied, modified, or distributed
// except according to those terms.

use thiserror::Error;

#[derive(Debug, Error)]
pub enum CatfishError {
    #[error("{0}")]
    ValidationError(String),

    #[error("{1}")]
    UnexpectedError(#[source] Box<dyn std::error::Error>, String),
}
