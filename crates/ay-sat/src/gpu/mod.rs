// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GPU compute infrastructure for SAT acceleration experiments.
//!
//! This module provides a minimal `wgpu` abstraction for Phase 7:
//! - Device and queue initialization
//! - WGSL compute shader loading
//! - Storage/readback buffer helpers
//! - Compute pipeline dispatch

#[cfg(test)]
pub(crate) mod pdr_push;
pub(crate) mod subsume;

use std::error::Error;
use std::fmt;
use std::mem::size_of;
use std::sync::mpsc;
use std::time::Duration;

const MAP_READ_TIMEOUT: Duration = Duration::from_secs(5);

/// Backends targeted by AY Phase 7 GPU support.
///
/// NVIDIA hardware is supported through the Vulkan/DX12 backends in `wgpu`.
pub(crate) fn supported_backends() -> wgpu::Backends {
    wgpu::Backends::METAL | wgpu::Backends::VULKAN | wgpu::Backends::DX12
}

/// Errors returned by GPU context and compute helpers.
#[derive(Debug)]
#[non_exhaustive]
pub(crate) enum GpuError {
    /// No compatible adapter was found for the requested backend mask.
    AdapterUnavailable {
        /// Backend mask used for adapter discovery.
        backends: wgpu::Backends,
    },
    /// Device creation failed.
    RequestDevice(wgpu::RequestDeviceError),
    /// Readback buffer mapping failed.
    BufferMap(wgpu::BufferAsyncError),
    /// Readback operation timed out while waiting for map completion.
    ReadbackTimeout,
    /// Readback size does not match requested output length.
    ReadbackSizeMismatch {
        /// Expected byte length.
        expected: usize,
        /// Actual mapped byte length.
        actual: usize,
    },
    /// GPU subsumption would require an output buffer above the configured cap.
    SubsumptionResultBufferTooLarge {
        /// Number of active clauses considered for pairwise subsumption.
        num_clauses: usize,
        /// Required bitset result buffer size in bytes.
        result_bytes: usize,
        /// Configured maximum bitset result buffer size in bytes.
        max_result_bytes: usize,
    },
    /// GPU BVE dispatch would exceed a device limit (storage-buffer binding
    /// size or compute workgroup count). Callers fall back to the CPU path.
    BveDispatchTooLarge {
        /// Number of (pos, neg) resolution pairs requested.
        num_pairs: usize,
        /// Largest required buffer size in bytes.
        required_bytes: u64,
        /// Device maximum storage-buffer binding size in bytes.
        max_binding_bytes: u64,
    },
    /// Requested output length cannot be represented as a byte size.
    OutputSizeOverflow {
        /// Requested `u32` element count.
        len: usize,
    },
}

impl fmt::Display for GpuError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AdapterUnavailable { backends } => {
                write!(f, "no GPU adapter available for backends {backends:?}")
            }
            Self::RequestDevice(error) => write!(f, "request_device failed: {error}"),
            Self::BufferMap(error) => write!(f, "buffer map failed: {error}"),
            Self::ReadbackTimeout => write!(f, "timed out waiting for GPU readback map"),
            Self::ReadbackSizeMismatch { expected, actual } => {
                write!(
                    f,
                    "GPU readback size mismatch: expected {expected} bytes, got {actual} bytes"
                )
            }
            Self::SubsumptionResultBufferTooLarge {
                num_clauses,
                result_bytes,
                max_result_bytes,
            } => write!(
                f,
                "GPU subsumption result bitset for {num_clauses} clauses needs {result_bytes} bytes, above cap {max_result_bytes} bytes"
            ),
            Self::BveDispatchTooLarge {
                num_pairs,
                required_bytes,
                max_binding_bytes,
            } => write!(
                f,
                "GPU BVE dispatch for {num_pairs} pairs needs {required_bytes} bytes, above device binding limit {max_binding_bytes} bytes"
            ),
            Self::OutputSizeOverflow { len } => write!(
                f,
                "GPU buffer size overflow while converting {len} u32 values to bytes"
            ),
        }
    }
}

impl Error for GpuError {}

/// Binding descriptor for storage buffers used by compute shaders.
#[derive(Clone, Copy, Debug)]
pub(crate) struct StorageBinding {
    /// Binding slot index in the bind group.
    pub(crate) binding: u32,
    /// Whether the storage buffer is read-only from shader code.
    pub(crate) read_only: bool,
}

/// Bind group entry for a buffer resource.
#[derive(Clone, Copy, Debug)]
pub(crate) struct BufferBinding<'a> {
    /// Binding slot index in the bind group.
    pub(crate) binding: u32,
    /// Backing buffer for the binding slot.
    pub(crate) buffer: &'a wgpu::Buffer,
}

/// Initialized GPU context for compute workloads.
#[derive(Debug)]
pub(crate) struct GpuContext {
    device: wgpu::Device,
    queue: wgpu::Queue,
    info: wgpu::AdapterInfo,
}

impl GpuContext {
    /// Initializes a GPU context with the default backend set for Phase 7.
    pub(crate) fn initialize() -> Result<Self, GpuError> {
        Self::initialize_with_backends(supported_backends())
    }

    /// Initializes a GPU context with an explicit backend mask.
    pub(crate) fn initialize_with_backends(backends: wgpu::Backends) -> Result<Self, GpuError> {
        pollster::block_on(Self::initialize_async(backends))
    }

    async fn initialize_async(backends: wgpu::Backends) -> Result<Self, GpuError> {
        let instance = wgpu::Instance::new(wgpu::InstanceDescriptor {
            backends,
            ..Default::default()
        });

        let adapter = instance
            .request_adapter(&wgpu::RequestAdapterOptions {
                power_preference: wgpu::PowerPreference::HighPerformance,
                force_fallback_adapter: false,
                compatible_surface: None,
            })
            .await
            .ok_or(GpuError::AdapterUnavailable { backends })?;

        let info = adapter.get_info();
        let (device, queue) = adapter
            .request_device(
                &wgpu::DeviceDescriptor {
                    label: Some("ay-gpu-device"),
                    required_features: wgpu::Features::empty(),
                    required_limits: wgpu::Limits::default(),
                },
                None,
            )
            .await
            .map_err(GpuError::RequestDevice)?;

        Ok(Self {
            device,
            queue,
            info,
        })
    }

    /// Returns backend metadata for the selected adapter.
    pub(crate) fn adapter_info(&self) -> &wgpu::AdapterInfo {
        &self.info
    }

    /// Returns the selected backend type.
    pub(crate) fn backend(&self) -> wgpu::Backend {
        self.info.backend
    }

    /// Returns the limits negotiated for the device.
    pub(crate) fn limits(&self) -> wgpu::Limits {
        self.device.limits()
    }

    /// Creates a shader module from WGSL source text.
    pub(crate) fn create_shader_module(&self, label: &str, source: &str) -> wgpu::ShaderModule {
        self.device
            .create_shader_module(wgpu::ShaderModuleDescriptor {
                label: Some(label),
                source: wgpu::ShaderSource::Wgsl(source.into()),
            })
    }

    /// Creates a storage buffer with copy-in/copy-out usage bits.
    pub(crate) fn create_storage_buffer(&self, label: &str, size_bytes: u64) -> wgpu::Buffer {
        self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some(label),
            size: size_bytes,
            usage: wgpu::BufferUsages::STORAGE
                | wgpu::BufferUsages::COPY_SRC
                | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        })
    }

    /// Creates a storage buffer and initializes it with `u32` data.
    pub(crate) fn create_storage_buffer_from_u32(
        &self,
        label: &str,
        values: &[u32],
    ) -> Result<wgpu::Buffer, GpuError> {
        let bytes = encode_u32(values);
        let size_bytes = u64::try_from(bytes.len())
            .map_err(|_| GpuError::OutputSizeOverflow { len: values.len() })?;
        let buffer = self.create_storage_buffer(label, size_bytes);
        self.queue.write_buffer(&buffer, 0, &bytes);
        Ok(buffer)
    }

    /// Creates a mappable buffer for host-side readback.
    pub(crate) fn create_readback_buffer(&self, label: &str, size_bytes: u64) -> wgpu::Buffer {
        self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some(label),
            size: size_bytes,
            usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
            mapped_at_creation: false,
        })
    }

    /// Creates a bind group layout for storage buffers.
    pub(crate) fn create_storage_bind_group_layout(
        &self,
        label: &str,
        bindings: &[StorageBinding],
    ) -> wgpu::BindGroupLayout {
        let entries: Vec<_> = bindings
            .iter()
            .map(|binding| wgpu::BindGroupLayoutEntry {
                binding: binding.binding,
                visibility: wgpu::ShaderStages::COMPUTE,
                ty: wgpu::BindingType::Buffer {
                    ty: wgpu::BufferBindingType::Storage {
                        read_only: binding.read_only,
                    },
                    has_dynamic_offset: false,
                    min_binding_size: None,
                },
                count: None,
            })
            .collect();

        self.device
            .create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some(label),
                entries: &entries,
            })
    }

    /// Creates a bind group from buffer bindings.
    pub(crate) fn create_bind_group(
        &self,
        label: &str,
        layout: &wgpu::BindGroupLayout,
        bindings: &[BufferBinding<'_>],
    ) -> wgpu::BindGroup {
        let entries: Vec<_> = bindings
            .iter()
            .map(|binding| wgpu::BindGroupEntry {
                binding: binding.binding,
                resource: binding.buffer.as_entire_binding(),
            })
            .collect();

        self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some(label),
            layout,
            entries: &entries,
        })
    }

    /// Creates a compute pipeline for a shader entry point.
    pub(crate) fn create_compute_pipeline(
        &self,
        label: &str,
        shader: &wgpu::ShaderModule,
        entry_point: &str,
        bind_group_layouts: &[&wgpu::BindGroupLayout],
    ) -> wgpu::ComputePipeline {
        let layout = self
            .device
            .create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: Some(label),
                bind_group_layouts,
                push_constant_ranges: &[],
            });

        self.device
            .create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some(label),
                layout: Some(&layout),
                module: shader,
                entry_point,
            })
    }

    /// Dispatches a compute pass with the provided pipeline and bind group.
    pub(crate) fn dispatch_compute(
        &self,
        label: &str,
        pipeline: &wgpu::ComputePipeline,
        bind_group: &wgpu::BindGroup,
        workgroups: (u32, u32, u32),
    ) {
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor { label: Some(label) });

        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some(label),
                timestamp_writes: None,
            });
            pass.set_pipeline(pipeline);
            pass.set_bind_group(0, bind_group, &[]);
            pass.dispatch_workgroups(workgroups.0, workgroups.1, workgroups.2);
        }

        self.queue.submit(Some(encoder.finish()));
    }

    /// Copies a device buffer to a readback buffer and decodes `u32` values.
    pub(crate) fn read_u32_buffer(
        &self,
        source: &wgpu::Buffer,
        len: usize,
    ) -> Result<Vec<u32>, GpuError> {
        if len == 0 {
            return Ok(Vec::new());
        }

        let size_bytes = byte_len_u32(len)?;
        let staging = self.create_readback_buffer("ay-gpu-readback", size_bytes);
        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("ay-gpu-readback-copy"),
            });
        encoder.copy_buffer_to_buffer(source, 0, &staging, 0, size_bytes);
        self.queue.submit(Some(encoder.finish()));
        self.read_u32_from_staging(&staging, len)
    }

    fn read_u32_from_staging(
        &self,
        staging: &wgpu::Buffer,
        len: usize,
    ) -> Result<Vec<u32>, GpuError> {
        let slice = staging.slice(..);
        let (sender, receiver) = mpsc::channel();
        slice.map_async(wgpu::MapMode::Read, move |result| {
            let _ = sender.send(result);
        });
        self.device.poll(wgpu::Maintain::Wait);

        match receiver.recv_timeout(MAP_READ_TIMEOUT) {
            Ok(Ok(())) => {}
            Ok(Err(error)) => return Err(GpuError::BufferMap(error)),
            Err(_) => return Err(GpuError::ReadbackTimeout),
        }

        let expected = usize::try_from(byte_len_u32(len)?)
            .map_err(|_| GpuError::OutputSizeOverflow { len })?;
        let data = slice.get_mapped_range();
        if data.len() < expected {
            let actual = data.len();
            drop(data);
            staging.unmap();
            return Err(GpuError::ReadbackSizeMismatch { expected, actual });
        }

        let values = decode_u32(&data[..expected]);
        drop(data);
        staging.unmap();
        Ok(values)
    }
}

fn byte_len_u32(len: usize) -> Result<u64, GpuError> {
    let bytes = len
        .checked_mul(size_of::<u32>())
        .ok_or(GpuError::OutputSizeOverflow { len })?;
    u64::try_from(bytes).map_err(|_| GpuError::OutputSizeOverflow { len })
}

fn encode_u32(values: &[u32]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(size_of_val(values));
    for value in values {
        bytes.extend_from_slice(&value.to_le_bytes());
    }
    bytes
}

fn decode_u32(bytes: &[u8]) -> Vec<u32> {
    bytes
        .chunks_exact(size_of::<u32>())
        .map(|chunk| {
            let mut word = [0_u8; size_of::<u32>()];
            word.copy_from_slice(chunk);
            u32::from_le_bytes(word)
        })
        .collect()
}

pub(crate) mod bve;

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "tests.rs"]
mod tests;

#[allow(clippy::panic)]
#[cfg(test)]
mod integration_tests;
