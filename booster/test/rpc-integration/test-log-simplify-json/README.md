# Testing logging of equations as JSON

This test sends the request to simplify an initial configuration of a Kontrol proof (based on the `resources/foundry-bug-report.kore` definition).
The `kore-rpc-booster` server is expected to be started with `-l SimplifyJson --log-file test-log-simplify-json/simplify-log.txt`, which ensures that the equation simplification logs are collected by both Booster and Kore and emitted into a file. The log file is compared to `simplify-log.golden.txt`.

Note: this test may turn out to be flaky, as the logs are sensitive to which equations fail to apply in Booster and why.

