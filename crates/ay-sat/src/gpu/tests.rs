// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;

use super::{BufferBinding, GpuContext, GpuError, StorageBinding};

const VECTOR_ADD_SHADER: &str = r#"
@group(0) @binding(0) var<storage, read> lhs: array<u32>;
@group(0) @binding(1) var<storage, read> rhs: array<u32>;
@group(0) @binding(2) var<storage, read_write> out_buf: array<u32>;

@compute @workgroup_size(1)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
let idx = gid.x;
out_buf[idx] = lhs[idx] + rhs[idx];
}
"#;

#[test]
fn vector_add_compute_shader_executes() {
    let context = match GpuContext::initialize() {
        Ok(context) => context,
        Err(GpuError::AdapterUnavailable { .. }) => return,
        Err(error) => panic!("GPU initialization failed: {error}"),
    };

    assert!(matches!(
        context.backend(),
        wgpu::Backend::Metal | wgpu::Backend::Vulkan | wgpu::Backend::Dx12
    ));

    let lhs: Vec<u32> = (1_u32..=16_u32).collect();
    let rhs: Vec<u32> = (101_u32..=116_u32).collect();
    let expected: Vec<u32> = lhs.iter().zip(rhs.iter()).map(|(a, b)| a + b).collect();

    let lhs_buffer = context
        .create_storage_buffer_from_u32("vector-add-lhs", &lhs)
        .expect("lhs buffer creation must succeed");
    let rhs_buffer = context
        .create_storage_buffer_from_u32("vector-add-rhs", &rhs)
        .expect("rhs buffer creation must succeed");
    let out_buffer = context
        .create_storage_buffer_from_u32("vector-add-out", &vec![0_u32; lhs.len()])
        .expect("output buffer creation must succeed");

    let layout = context.create_storage_bind_group_layout(
        "vector-add-layout",
        &[
            StorageBinding {
                binding: 0,
                read_only: true,
            },
            StorageBinding {
                binding: 1,
                read_only: true,
            },
            StorageBinding {
                binding: 2,
                read_only: false,
            },
        ],
    );

    let bind_group = context.create_bind_group(
        "vector-add-bind-group",
        &layout,
        &[
            BufferBinding {
                binding: 0,
                buffer: &lhs_buffer,
            },
            BufferBinding {
                binding: 1,
                buffer: &rhs_buffer,
            },
            BufferBinding {
                binding: 2,
                buffer: &out_buffer,
            },
        ],
    );

    let shader = context.create_shader_module("vector-add-wgsl", VECTOR_ADD_SHADER);
    let pipeline =
        context.create_compute_pipeline("vector-add-pipeline", &shader, "main", &[&layout]);
    let workgroups_x = u32::try_from(lhs.len()).expect("workgroup count must fit in u32");
    context.dispatch_compute(
        "vector-add-dispatch",
        &pipeline,
        &bind_group,
        (workgroups_x, 1, 1),
    );

    let actual = context
        .read_u32_buffer(&out_buffer, lhs.len())
        .expect("readback must succeed");
    assert_eq!(actual, expected);
}
