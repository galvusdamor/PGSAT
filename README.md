# PGSAT (Partially Grounded SAT)

PGSAT is a planner that encodes planning problems into SAT formulas. It keeps actions at a lifted level while grounding predicates either fully or partially.

## Installation

1. Clone the following repositories:
   - PGSAT (this repository)
      ```bash
      ```
   - [CPDDL](https://gitlab.com/danfis/cpddl/-/tree/master?ref_type=heads)
      ```bash
      git clone https://gitlab.com/danfis/cpddl.git
      ```
   - [Kissat](https://github.com/arminbiere/kissat?tab=readme-ov-file)
      ```bash
      git clone https://github.com/arminbiere/kissat.git
      ```

2. Build CPDDL and Kissat by following the installation instructions provided in their respective repositories.

3. After building CPDDL and Kissat, you can build the PGSAT planner with the following command:
  ```bash
  ./build.py [-d] -s path/to/kissat/build/ -c path/to/cpddl
  ```

   The `-d` flag is optional. It indicates whether to perform a debug build. Use `-d` for a debug build, or omit the flag for a release build.

4. Make sure to replace the paths with the correct locations of your local Kissat and CPDDL builds.

## Usage

To use the PGSAT planner, run the following command:

```bash
./powerlifted.py [--debug] -d path/to/domain_file -i path/to/instance_file -s pgsat -o [-F] [-G] [-b]
```

### Command Options:

- `--debug` (optional): Enables debug mode. Use this flag for detailed logging.

- `-d path/to/domain_file`: Specifies the path to the domain file.

- `-i path/to/instance_file`: Specifies the path to the instance file.

- `-s pgsat`: Specifies PGSAT is the planner to use.

- `-o`: Specifies the planner has to run in optimal mode.

### Optional Flags:

- `-F`: Disables generation of Lifted FAM Groups, thus generating the encoding with fully grounded facts.

- `-G`: Disables the preprocessing technique of predicate pruning.

- `-b`: Uses a binary encoding for objects. Must be used together with the flag "-F".
