# **Lean Project Setup** 🏗️️

This section describes the steps we took to set up our Lean project.  The resulting
source code is maintained in our lean4crypto respository at

<https://github.com/formalverification/lean4crypto>

1.  **Create the Project**.

    In a terminal,
    ```bash
    lake new OTP math
    cd OTP
    ```

2.  **Verfiy Mathlib Dependency**.

    The `lakefile.toml` should look something like this:

    ```toml
    name = "OTP"
    version = "0.1.0"
    keywords = ["math"]
    defaultTargets = ["OTP"]

    [leanOptions]
    pp.unicode.fun = true # pretty-prints `fun a ↦ b`
    autoImplicit = false

    [[require]]
    name = "mathlib"
    scope = "leanprover-community"

    [[lean_lib]]
    name = "OTP"
    ```

3.  **Fetch Mathlib:**
    In your terminal (in the `otp_formalization` directory):
    ```bash
    lake update
    ```
    This might take a few minutes the first time. Then build to ensure it's working:
    ```bash
    lake build
    ```

4.  **Create Main File**.

    * The `lake new` command creates `OTP.lean` and `OTP/Basic.lean`.
    * We'll start the formalization in `OTP/Basic.lean` which is imported into `OTP.lean`.





