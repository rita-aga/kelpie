"""Setup script for kelpie-letta adapter.

This package provides a compatibility layer allowing Letta clients to connect
to Kelpie servers. It enables using the `letta-client` SDK with Kelpie as a
drop-in replacement for Letta server.

Installation:
    pip install -e adapters/letta/

Usage:
    from letta_client import Letta

    # Connect to Kelpie server instead of Letta
    client = Letta(base_url="http://localhost:8283")

    # Use as normal Letta client
    agent = client.agents.create(name="my-agent")
"""

from setuptools import setup, find_packages

setup(
    name="kelpie-letta",
    version="0.1.0",
    description="Letta compatibility layer for Kelpie agent runtime",
    author="nerdsane",
    author_email="",
    url="https://github.com/nerdsane/kelpie",
    packages=find_packages(),
    python_requires=">=3.10",
    install_requires=[
        "requests>=2.28.0",
    ],
    extras_require={
        "test": [
            "pytest>=7.0.0",
            "pytest-asyncio>=0.21.0",
            "letta-client>=0.1.0",
        ],
        "dev": [
            "pytest>=7.0.0",
            "pytest-asyncio>=0.21.0",
            "letta-client>=0.1.0",
            "mypy>=1.0.0",
            "black>=23.0.0",
        ],
    },
    classifiers=[
        "Development Status :: 3 - Alpha",
        "Intended Audience :: Developers",
        "License :: OSI Approved :: Apache Software License",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Programming Language :: Python :: 3.12",
    ],
)
