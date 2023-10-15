# Libra
## Install
Libra requires SBT to build. SBT can be installed using
[these](https://www.scala-sbt.org/index.html) directions. To install Libra, run
`sbt assembly` in the top level directory.

## Usage
Libra can be run on a benchmark by using the provided `run_libra.sh` script. A
couple benchmarks are provided in the `test/` directory. Use the following
commands to evaluate against a benchmark:

```sh
./run_libra.sh test/body_builder/op269.rules.small.dl logs/
```
