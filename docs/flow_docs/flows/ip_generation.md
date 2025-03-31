# IP generation

There is a [`cookiecutter`](https://cookiecutter.readthedocs.io/en/stable/) setup for generating a base skeleton for an
IP directory.

## Installing cookiecutter

To use IP generation flow your environment needs to be able to execute `cookiecutter`. To achieve this there are currently multiple
possibilities:

1. Use a virtual environment and install the `cookiecutter` package via `pip`
2. Have it part of your user installed pip packages, e.g. `pipx`, see doc of cookiecutter
3. Use the provided module

### Install in virtual environment

The recipe to install in a virtual environment on Hetzner is as follows:

**One-time setup** to create a venv for cookiecutter:

```shell
module switch python/3.10.13
# Create virtual environment
python3 -m venv .venv-cookiecutter
# Activate virtual environment
source .venv-cookiecutter/bin/activate
# Install cookiecutter
pip3 install cookiecutter
```

### Reactivate virtual environment

To re-use the virtual environment installation you only need to `activate` each time a new shell is opened:

```shell
module switch python/3.10.13
# Activate virtual environment
source .venv-cookiecutter/bin/activate
```

### Use provided module

Use `module` to load a pre-packaged cookiecutter installation:

```shell
# List available releases
module avail cookiecutter -l
# Show release information
module show cookiecutter/2.6
# Switch to one of the releases
module load cookiecutter/2.6
```

## Using cookiecutter

Go into the directory where the IP should be added and execute cookiecutter.
The argument has to point to a provided template structure.

```shell
cd hw/ip
cookiecutter ../scripts/cookiecutter/ip_directory
```

Now follow the prompt of cookiecutter and you will have the directory skeleton generated!

## Deactivating cookiecutter

When done, unload the module or deactivate the virtual environment:

### Module

```shell
module unload cookiecutter
```

### Virtual environment

```shell
deactivate
```




