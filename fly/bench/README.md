# OCaml GC Benchmark Suite

Compare Verified GC OCaml vs Stock OCaml performance.

## Structure

```
bench/
├── benchmark.py       # Main Python module
├── tests/             # OCaml benchmark programs
│   ├── binarytrees.ml      # GC stress test (trees)
│   ├── alloc_stress.ml     # Heavy allocation
│   ├── multicore_alloc.ml  # Multicore domains
│   ├── linkedlist.ml       # Pointer-heavy data
│   ├── hashtbl_stress.ml   # Hash table operations
│   ├── array_ops.ml        # Array operations
│   ├── recursive_fib.ml    # Memoized Fibonacci
│   ├── string_concat.ml    # String operations
│   ├── fannkuchredux.ml    # Benchmarks Game - permutations
│   ├── nbody.ml            # Benchmarks Game - n-body
│   ├── spectralnorm.ml     # Benchmarks Game - spectral norm
│   ├── fasta.ml            # Benchmarks Game - FASTA
│   ├── knucleotide.ml      # Benchmarks Game - k-nucleotide
│   └── revcomp.ml          # Benchmarks Game - reverse-complement
├── build/             # Compiled binaries (auto-generated)
└── README.md
```

## Usage

### In Jupyter Notebook

```python
from benchmark import BenchmarkSuite

# Initialize suite
suite = BenchmarkSuite()

# Run all benchmarks
results = suite.run_all()

# Plot comparison
fig = suite.plot_comparison(results)

# Plot speedup chart
fig = suite.plot_speedup(results)

# Generate markdown report
report = suite.generate_report(results, output_dir="./report")
```

### Command Line

```bash
# Run all benchmarks
python benchmark.py

# Run specific benchmarks
python benchmark.py --benchmarks binarytrees alloc_stress

# Save report
python benchmark.py --output ./report

# Custom compiler paths
python benchmark.py --verified ~/local/ocaml-verified-gc/bin/ocamlopt \
                    --stock ~/.opam/5.3.0/bin/ocamlopt
```

## Benchmarks

### Custom Benchmarks

| Name | Description |
|------|-------------|
| `binarytrees` | Classic GC stress test - many short-lived tree nodes |
| `alloc_stress` | Heavy allocation - millions of small objects |
| `multicore_alloc` | Multicore - multiple domains allocating concurrently |
| `linkedlist` | Linked list - pointer-heavy data structure |
| `hashtbl_stress` | Hash table - insertions, lookups, deletions |
| `array_ops` | Array operations - map, filter, fold |
| `recursive_fib` | Memoized Fibonacci - hash table allocations |
| `string_concat` | String operations - many string allocations |

### Benchmarks Game

| Name | Description | Source |
|------|-------------|--------|
| `fannkuchredux` | Permutations with flips | [link](https://benchmarksgame-team.pages.debian.net/benchmarksgame/performance/fannkuchredux.html) |
| `nbody` | N-body simulation | [link](https://benchmarksgame-team.pages.debian.net/benchmarksgame/performance/nbody.html) |
| `spectralnorm` | Spectral norm calculation | [link](https://benchmarksgame-team.pages.debian.net/benchmarksgame/performance/spectralnorm.html) |
| `fasta` | FASTA sequence generation | [link](https://benchmarksgame-team.pages.debian.net/benchmarksgame/performance/fasta.html) |
| `knucleotide` | K-nucleotide frequency | [link](https://benchmarksgame-team.pages.debian.net/benchmarksgame/performance/knucleotide.html) |
| `revcomp` | Reverse-complement | [link](https://benchmarksgame-team.pages.debian.net/benchmarksgame/performance/revcomp.html) |

## API Reference

### BenchmarkSuite

```python
class BenchmarkSuite:
    def __init__(
        verified_ocaml: str = None,  # Auto-detect if None
        stock_ocaml: str = None,     # Auto-detect if None
        tests_dir: str = None,        # Default: ./tests
        build_dir: str = None         # Default: ./build
    )
    
    def run_all(
        benchmarks: List[str] = None,  # None = all
        warmup: int = 2,
        runs: int = 5
    ) -> Dict[str, Tuple[BenchmarkResult, BenchmarkResult]]
    
    def run_single(benchmark_name: str) -> Tuple[BenchmarkResult, BenchmarkResult]
    
    def plot_comparison(results) -> Figure
    def plot_speedup(results) -> Figure
    def plot_times_distribution(results, benchmark_name) -> Figure
    def plot_all_distributions(results) -> Figure
    def generate_report(results, output_dir=None) -> str
```

### BenchmarkResult

```python
@dataclass
class BenchmarkResult:
    name: str
    variant: str       # 'verified' or 'stock'
    times: List[float] # Individual run times (ms)
    mean: float
    std: float
    min: float
    max: float
```
