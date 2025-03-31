# Documentation

The documentation environment is managed with [frankenstein](https://git.axelera.ai/tools/py/dev/frankenstein).
For more information on how to use `frankenstein`, please refer to the [documentation](https://doc.axelera.ai/tools/py/dev/frankenstein/latest/user_guide/start/).

To render the documentation locally:

1. Load the `frankenstein` module (once per shell):

    ```shell
    module load axelera-frankenstein
    ```

2. Run the server in port 45432 (or replace `-p` option for a different port):

    ```shell
    frankenstein docs serve -p 45432
    ```


You can see the `frankenstein` **help** message by running:

```
frankenstein docs -h
```
