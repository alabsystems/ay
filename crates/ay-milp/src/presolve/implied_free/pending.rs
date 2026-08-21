// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

std::thread_local! {
    static PENDING_AFFINE_AGGREGATION_CERTIFICATE:
        std::cell::RefCell<Option<AffineAggregationCertificate>> = const {
            std::cell::RefCell::new(None)
        };
}

pub(crate) fn clear_pending_certificate() {
    PENDING_AFFINE_AGGREGATION_CERTIFICATE.with(|slot| {
        slot.borrow_mut().take();
    });
}

pub(crate) fn set_pending_certificate(certificate: AffineAggregationCertificate) {
    PENDING_AFFINE_AGGREGATION_CERTIFICATE.with(|slot| {
        *slot.borrow_mut() = Some(certificate);
    });
}

pub(crate) fn take_pending_certificate() -> Option<AffineAggregationCertificate> {
    PENDING_AFFINE_AGGREGATION_CERTIFICATE.with(|slot| slot.borrow_mut().take())
}
