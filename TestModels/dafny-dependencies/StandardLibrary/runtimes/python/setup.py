# Lightweight setup.py that installs the version of DafnyRuntimePython specified in project.properties.
# .toml does not support dynamically loading version strings from another file.

from setuptools import setup

def get_dafny_runtime_version():
    """Reads the dafnyVersion from project.properties."""
    with open("../../project.properties", "r") as version_file:
        for line in version_file:
            if line.startswith("dafnyVersion="):
                # Split the line on the equals sign and return the version (right-hand side)
                return line.split("=")[1].strip()
    raise ValueError("dafnyVersion not found in project.properties")

# Only specifying the DafnyRuntime dependency with dynamic version
setup(
    install_requires=[
        f"DafnyRuntimePython=={get_dafny_runtime_version()}"
    ]
)