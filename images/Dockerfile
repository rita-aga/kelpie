# Kelpie Base Image - Alpine Linux
#
# Multi-arch VM image for teleportable sandboxes
# Supports: linux/arm64, linux/amd64
#
# TigerStyle: Explicit versions, minimal layers, reproducible builds

# Build arguments for versioning
ARG ALPINE_VERSION=3.19
ARG BUILD_DATE
ARG VERSION
ARG GIT_SHA

# Stage 1: Builder
FROM alpine:${ALPINE_VERSION} AS builder

# Install build dependencies
RUN apk add --no-cache \
    alpine-sdk \
    rust \
    cargo \
    musl-dev

# Create build directory
WORKDIR /build

# Copy guest agent source (will be added in Phase 5.2)
# COPY guest-agent/ /build/guest-agent/

# Build guest agent (will be enabled in Phase 5.2)
# RUN cd guest-agent && \
#     cargo build --release --target $(uname -m)-unknown-linux-musl && \
#     strip target/*/release/kelpie-guest

# Stage 2: Runtime Image
FROM alpine:${ALPINE_VERSION}

# Re-declare build args for this stage (required for labels)
ARG VERSION
ARG BUILD_DATE
ARG GIT_SHA
ARG ALPINE_VERSION

# Image metadata
LABEL org.opencontainers.image.title="Kelpie Base Image"
LABEL org.opencontainers.image.description="Minimal Alpine Linux VM image for Kelpie sandboxes"
LABEL org.opencontainers.image.version="${VERSION}"
LABEL org.opencontainers.image.created="${BUILD_DATE}"
LABEL org.opencontainers.image.revision="${GIT_SHA}"
LABEL org.kelpie.alpine.version="${ALPINE_VERSION}"

# Install essential runtime packages
# TigerStyle: Explicit package list, no wildcards
RUN apk add --no-cache \
    busybox \
    ca-certificates \
    coreutils \
    util-linux \
    shadow \
    bash \
    && rm -rf /var/cache/apk/*

# Create necessary directories
# TigerStyle: Explicit paths, clear ownership
RUN mkdir -p \
    /workspace \
    /tmp \
    /var/run \
    /var/log \
    && chmod 1777 /tmp \
    && chmod 755 /workspace

# Copy guest agent binary (will be enabled in Phase 5.2)
# COPY --from=builder /build/guest-agent/target/*/release/kelpie-guest /usr/local/bin/
# RUN chmod 755 /usr/local/bin/kelpie-guest

# Copy init script (Phase 5.3)
# Remove busybox symlink and install our custom init
RUN rm -f /sbin/init
COPY base/init /sbin/init
COPY base/hostname /etc/hostname
COPY base/fstab /etc/fstab
RUN chmod 755 /sbin/init && \
    chmod 644 /etc/hostname && \
    chmod 644 /etc/fstab

# Set up minimal environment
ENV PATH=/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin
ENV LANG=C.UTF-8
ENV LC_ALL=C.UTF-8

# Use init as PID 1
CMD ["/sbin/init"]

# Metadata for version tracking
ARG VERSION
ARG GIT_SHA
ARG BUILD_DATE
RUN echo "${VERSION}" > /etc/kelpie-version && \
    echo "${GIT_SHA}" > /etc/kelpie-git-sha && \
    echo "${BUILD_DATE}" > /etc/kelpie-build-date
