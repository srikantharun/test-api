# ICDF Stimuli Release

The ICDF stimuli releases can be found in the package registry of the ICDF project: https://git.axelera.ai/dev/rd/IntraCoreDataFlow/-/packages. Anyone with access to the ICDF repository can download the available stimuli there.

Alternatively, one can create a personal private GitLab access token (see [docs](https://docs.gitlab.com/ee/user/profile/personal_access_tokens.html#create-a-personal-access-token)) and use the following script to download the stimuli:

```bash
# Set GITLAB_API_TOKEN to your personal private token first
./scripts/stimuli/download_stimuli.sh -r <release_version> -p <package_name> -f <file_name> -o <output_dir>
```

The following arguments are available:

- `-r`: The release version for which the stimuli should be downloaded (e.g. 7.0).
- `-p`: The package from which the stimuli should be downloaded.
- `-f`: The specific file name of the tarball containing the stimuli.
- `-0`: The directory where the stimuli should be placed. The default value is `.`.

Below is a table listing the available packages and files for the Europa project:

| Stimuli            | Package   | File Name                                    |
| ------------------ | --------- | -------------------------------------------- |
| `rtl-tb`           | `stimuli` | `stimuli_europa_rtl_tb_functional.tar.gz`    |
| `fiat`             | `stimuli` | `stimuli_europa_fiat_functional.tar.gz`      |
| `drv-fiat`         | `stimuli` | `stimuli_europa_drv_fiat_functional.tar.gz`  |
| `perf-eval`        | `stimuli` | `stimuli_europa_drv_fiat_performance.tar.gz` |
| `functional-atex`  | `atex`    | `atex_europa_functional.tar.gz`              |
| `performance-atex` | `atex`    | `atex_europa_performance.tar.gz`             |
