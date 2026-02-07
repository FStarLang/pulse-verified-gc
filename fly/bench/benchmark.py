"""
benchmark.py - OCaml GC Benchmark Suite

This module provides utilities for running benchmarks comparing
the verified GC OCaml vs stock OCaml, with matplotlib visualization.

Usage in Jupyter notebook:
    from benchmark import BenchmarkSuite
    suite = BenchmarkSuite()
    results = suite.run_all()
    suite.plot_comparison(results)
"""

import subprocess
import time
import os
import shutil
import tempfile
import json
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional, Dict, List, Tuple
import statistics

# Try to import matplotlib (optional for running benchmarks)
try:
    import matplotlib.pyplot as plt
    import matplotlib.patches as mpatches
    import numpy as np
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False
    print("Warning: matplotlib not available. Plotting disabled.")


@dataclass
class BenchmarkResult:
    """Result of a single benchmark run."""
    name: str
    variant: str  # 'verified' or 'stock'
    times: List[float] = field(default_factory=list)
    mean: float = 0.0
    std: float = 0.0
    min: float = 0.0
    max: float = 0.0
    
    def compute_stats(self):
        if self.times:
            self.mean = statistics.mean(self.times)
            self.std = statistics.stdev(self.times) if len(self.times) > 1 else 0.0
            self.min = min(self.times)
            self.max = max(self.times)


@dataclass 
class BenchmarkConfig:
    """Configuration for a benchmark."""
    name: str
    source_file: str
    args: List[str] = field(default_factory=list)
    warmup_runs: int = 2
    timed_runs: int = 5
    description: str = ""


class BenchmarkSuite:
    """
    OCaml GC Benchmark Suite
    
    Compares verified GC OCaml against stock OCaml on various workloads.
    """
    
    # Default benchmark configurations
    DEFAULT_BENCHMARKS = [
        BenchmarkConfig(
            name="binarytrees",
            source_file="binarytrees.ml",
            args=["18"],
            description="Classic GC stress test - many short-lived tree nodes"
        ),
        BenchmarkConfig(
            name="alloc_stress",
            source_file="alloc_stress.ml",
            args=["5000000"],
            description="Heavy allocation - 5M small object allocations"
        ),
        BenchmarkConfig(
            name="multicore_alloc",
            source_file="multicore_alloc.ml",
            args=["4", "50000"],
            description="Multicore - 4 domains allocating concurrently"
        ),
        BenchmarkConfig(
            name="linkedlist",
            source_file="linkedlist.ml",
            args=["500000"],
            description="Linked list - pointer-heavy data structure"
        ),
        BenchmarkConfig(
            name="hashtbl_stress",
            source_file="hashtbl_stress.ml",
            args=["500000"],
            description="Hash table - insertions, lookups, deletions"
        ),
        BenchmarkConfig(
            name="array_ops",
            source_file="array_ops.ml",
            args=["5000000"],
            description="Array operations - map, filter, fold"
        ),
        BenchmarkConfig(
            name="recursive_fib",
            source_file="recursive_fib.ml",
            args=["40"],
            description="Memoized Fibonacci - hash table allocations"
        ),
        BenchmarkConfig(
            name="string_concat",
            source_file="string_concat.ml",
            args=["50000"],
            description="String operations - many string allocations"
        ),
        # === Benchmarks Game classics ===
        BenchmarkConfig(
            name="fannkuchredux",
            source_file="fannkuchredux.ml",
            args=["11"],
            description="Benchmarks Game - fannkuch-redux (permutations)"
        ),
        BenchmarkConfig(
            name="nbody",
            source_file="nbody.ml",
            args=["5000000"],
            description="Benchmarks Game - n-body simulation"
        ),
        BenchmarkConfig(
            name="spectralnorm",
            source_file="spectralnorm.ml",
            args=["3000"],
            description="Benchmarks Game - spectral norm calculation"
        ),
        BenchmarkConfig(
            name="fasta",
            source_file="fasta.ml",
            args=["1000000"],
            description="Benchmarks Game - FASTA sequence generation"
        ),
    ]
    
    def __init__(
        self,
        verified_ocaml: Optional[str] = None,
        stock_ocaml: Optional[str] = None,
        tests_dir: Optional[str] = None,
        build_dir: Optional[str] = None
    ):
        """
        Initialize benchmark suite.
        
        Args:
            verified_ocaml: Path to verified GC ocamlopt (auto-detect if None)
            stock_ocaml: Path to stock ocamlopt (auto-detect if None)
            tests_dir: Directory containing test .ml files
            build_dir: Directory for compiled binaries
        """
        # Find compilers
        self.verified_ocaml = verified_ocaml or self._find_verified_ocaml()
        self.stock_ocaml = stock_ocaml or self._find_stock_ocaml()
        
        # Set directories
        script_dir = Path(__file__).parent
        self.tests_dir = Path(tests_dir) if tests_dir else script_dir / "tests"
        self.build_dir = Path(build_dir) if build_dir else script_dir / "build"
        
        # Create build directory
        self.build_dir.mkdir(exist_ok=True)
        
        # Verify setup
        self._verify_setup()
    
    def _find_verified_ocaml(self) -> str:
        """Find verified GC ocamlopt."""
        candidates = [
            Path.home() / "local/ocaml-verified-gc/bin/ocamlopt",
            Path.home() / "ocaml-verified-gc/bin/ocamlopt",
        ]
        for path in candidates:
            if path.exists():
                return str(path)
        raise FileNotFoundError(
            "Could not find verified GC ocamlopt. "
            "Set verified_ocaml parameter explicitly."
        )
    
    def _find_stock_ocaml(self) -> str:
        """Find stock ocamlopt."""
        result = shutil.which("ocamlopt")
        if result:
            return result
        raise FileNotFoundError(
            "Could not find stock ocamlopt in PATH. "
            "Set stock_ocaml parameter explicitly."
        )
    
    def _verify_setup(self):
        """Verify compilers and tests exist."""
        if not os.path.exists(self.verified_ocaml):
            raise FileNotFoundError(f"Verified ocamlopt not found: {self.verified_ocaml}")
        if not os.path.exists(self.stock_ocaml):
            raise FileNotFoundError(f"Stock ocamlopt not found: {self.stock_ocaml}")
        if not self.tests_dir.exists():
            raise FileNotFoundError(f"Tests directory not found: {self.tests_dir}")
        
        print(f"Verified OCaml: {self.verified_ocaml}")
        print(f"Stock OCaml: {self.stock_ocaml}")
        print(f"Tests directory: {self.tests_dir}")
    
    def compile(self, config: BenchmarkConfig, variant: str) -> str:
        """
        Compile a benchmark.
        
        Args:
            config: Benchmark configuration
            variant: 'verified' or 'stock'
            
        Returns:
            Path to compiled binary
        """
        source = self.tests_dir / config.source_file
        if not source.exists():
            raise FileNotFoundError(f"Source file not found: {source}")
        
        output = self.build_dir / f"{config.name}_{variant}"
        compiler = self.verified_ocaml if variant == "verified" else self.stock_ocaml
        
        cmd = [compiler, "-O3", "-o", str(output), str(source)]
        
        try:
            subprocess.run(
                cmd,
                check=True,
                capture_output=True,
                text=True
            )
        except subprocess.CalledProcessError as e:
            print(f"Compilation failed for {config.name} ({variant})")
            print(f"stderr: {e.stderr}")
            raise
        
        return str(output)
    
    def run_benchmark(
        self,
        config: BenchmarkConfig,
        variant: str,
        binary: Optional[str] = None
    ) -> BenchmarkResult:
        """
        Run a benchmark multiple times and collect timing data.
        
        Args:
            config: Benchmark configuration
            variant: 'verified' or 'stock'
            binary: Path to binary (compile if None)
            
        Returns:
            BenchmarkResult with timing statistics
        """
        if binary is None:
            binary = self.compile(config, variant)
        
        result = BenchmarkResult(name=config.name, variant=variant)
        
        # Warmup runs
        for _ in range(config.warmup_runs):
            subprocess.run(
                [binary] + config.args,
                capture_output=True,
                check=True
            )
        
        # Timed runs
        for _ in range(config.timed_runs):
            start = time.perf_counter()
            subprocess.run(
                [binary] + config.args,
                capture_output=True,
                check=True
            )
            elapsed = time.perf_counter() - start
            result.times.append(elapsed * 1000)  # Convert to ms
        
        result.compute_stats()
        return result
    
    def run_single(
        self,
        benchmark_name: str,
        warmup: int = 2,
        runs: int = 5
    ) -> Tuple[BenchmarkResult, BenchmarkResult]:
        """
        Run a single benchmark for both variants.
        
        Args:
            benchmark_name: Name of benchmark (e.g., 'binarytrees')
            warmup: Number of warmup runs
            runs: Number of timed runs
            
        Returns:
            Tuple of (verified_result, stock_result)
        """
        config = None
        for c in self.DEFAULT_BENCHMARKS:
            if c.name == benchmark_name:
                config = c
                break
        
        if config is None:
            raise ValueError(f"Unknown benchmark: {benchmark_name}")
        
        config.warmup_runs = warmup
        config.timed_runs = runs
        
        print(f"Running {config.name}: {config.description}")
        
        verified = self.run_benchmark(config, "verified")
        stock = self.run_benchmark(config, "stock")
        
        return verified, stock
    
    def run_all(
        self,
        benchmarks: Optional[List[str]] = None,
        warmup: int = 2,
        runs: int = 5,
        verbose: bool = True
    ) -> Dict[str, Tuple[BenchmarkResult, BenchmarkResult]]:
        """
        Run all benchmarks.
        
        Args:
            benchmarks: List of benchmark names (None = all)
            warmup: Number of warmup runs
            runs: Number of timed runs
            verbose: Print progress
            
        Returns:
            Dict mapping benchmark name to (verified, stock) results
        """
        results = {}
        
        configs = self.DEFAULT_BENCHMARKS
        if benchmarks:
            configs = [c for c in configs if c.name in benchmarks]
        
        for config in configs:
            config.warmup_runs = warmup
            config.timed_runs = runs
            
            if verbose:
                print(f"\n{'='*60}")
                print(f"Benchmark: {config.name}")
                print(f"  {config.description}")
                print(f"  Args: {config.args}")
            
            try:
                verified = self.run_benchmark(config, "verified")
                stock = self.run_benchmark(config, "stock")
                
                results[config.name] = (verified, stock)
                
                if verbose:
                    speedup = stock.mean / verified.mean if verified.mean > 0 else 0
                    print(f"  Verified: {verified.mean:.2f} ± {verified.std:.2f} ms")
                    print(f"  Stock:    {stock.mean:.2f} ± {stock.std:.2f} ms")
                    print(f"  Speedup:  {speedup:.2f}x {'(verified faster)' if speedup > 1 else '(stock faster)'}")
                    
            except Exception as e:
                print(f"  ERROR: {e}")
        
        return results
    
    # =========================================================================
    # Plotting methods
    # =========================================================================
    
    def plot_comparison(
        self,
        results: Dict[str, Tuple[BenchmarkResult, BenchmarkResult]],
        figsize: Tuple[int, int] = (12, 6),
        title: str = "Verified GC vs Stock OCaml Performance"
    ) -> Optional[plt.Figure]:
        """
        Create a bar chart comparing verified vs stock performance.
        
        Args:
            results: Results from run_all()
            figsize: Figure size
            title: Plot title
            
        Returns:
            matplotlib Figure object
        """
        if not HAS_MATPLOTLIB:
            print("matplotlib not available")
            return None
        
        names = list(results.keys())
        verified_means = [results[n][0].mean for n in names]
        stock_means = [results[n][1].mean for n in names]
        verified_stds = [results[n][0].std for n in names]
        stock_stds = [results[n][1].std for n in names]
        
        x = np.arange(len(names))
        width = 0.35
        
        fig, ax = plt.subplots(figsize=figsize)
        
        bars1 = ax.bar(x - width/2, verified_means, width, 
                       yerr=verified_stds, label='Verified GC',
                       color='#2ecc71', capsize=3)
        bars2 = ax.bar(x + width/2, stock_means, width,
                       yerr=stock_stds, label='Stock OCaml',
                       color='#3498db', capsize=3)
        
        ax.set_xlabel('Benchmark')
        ax.set_ylabel('Time (ms)')
        ax.set_title(title)
        ax.set_xticks(x)
        ax.set_xticklabels(names, rotation=45, ha='right')
        ax.legend()
        ax.grid(axis='y', alpha=0.3)
        
        plt.tight_layout()
        return fig
    
    def plot_speedup(
        self,
        results: Dict[str, Tuple[BenchmarkResult, BenchmarkResult]],
        figsize: Tuple[int, int] = (10, 5),
        title: str = "Speedup: Verified GC vs Stock OCaml"
    ) -> Optional[plt.Figure]:
        """
        Create a bar chart showing speedup ratios.
        
        Speedup > 1 means verified is faster.
        Speedup < 1 means stock is faster.
        
        Args:
            results: Results from run_all()
            figsize: Figure size
            title: Plot title
            
        Returns:
            matplotlib Figure object
        """
        if not HAS_MATPLOTLIB:
            print("matplotlib not available")
            return None
        
        names = list(results.keys())
        speedups = []
        for n in names:
            v_mean = results[n][0].mean
            s_mean = results[n][1].mean
            speedups.append(s_mean / v_mean if v_mean > 0 else 1.0)
        
        fig, ax = plt.subplots(figsize=figsize)
        
        colors = ['#2ecc71' if s >= 1 else '#e74c3c' for s in speedups]
        bars = ax.bar(names, speedups, color=colors)
        
        ax.axhline(y=1.0, color='black', linestyle='--', linewidth=1)
        ax.set_xlabel('Benchmark')
        ax.set_ylabel('Speedup (higher = verified faster)')
        ax.set_title(title)
        ax.set_xticklabels(names, rotation=45, ha='right')
        ax.grid(axis='y', alpha=0.3)
        
        # Add value labels
        for bar, speedup in zip(bars, speedups):
            height = bar.get_height()
            ax.annotate(f'{speedup:.2f}x',
                        xy=(bar.get_x() + bar.get_width() / 2, height),
                        xytext=(0, 3),
                        textcoords="offset points",
                        ha='center', va='bottom', fontsize=9)
        
        # Add legend
        green_patch = mpatches.Patch(color='#2ecc71', label='Verified faster')
        red_patch = mpatches.Patch(color='#e74c3c', label='Stock faster')
        ax.legend(handles=[green_patch, red_patch], loc='upper right')
        
        plt.tight_layout()
        return fig
    
    def plot_times_distribution(
        self,
        results: Dict[str, Tuple[BenchmarkResult, BenchmarkResult]],
        benchmark_name: str,
        figsize: Tuple[int, int] = (8, 5)
    ) -> Optional[plt.Figure]:
        """
        Plot distribution of run times for a specific benchmark.
        
        Args:
            results: Results from run_all()
            benchmark_name: Name of benchmark to plot
            figsize: Figure size
            
        Returns:
            matplotlib Figure object
        """
        if not HAS_MATPLOTLIB:
            print("matplotlib not available")
            return None
        
        if benchmark_name not in results:
            print(f"Benchmark {benchmark_name} not found in results")
            return None
        
        verified, stock = results[benchmark_name]
        
        fig, ax = plt.subplots(figsize=figsize)
        
        positions = [1, 2]
        data = [verified.times, stock.times]
        
        bp = ax.boxplot(data, positions=positions, widths=0.5, patch_artist=True)
        
        bp['boxes'][0].set_facecolor('#2ecc71')
        bp['boxes'][1].set_facecolor('#3498db')
        
        ax.set_xticklabels(['Verified GC', 'Stock OCaml'])
        ax.set_ylabel('Time (ms)')
        ax.set_title(f'Time Distribution: {benchmark_name}')
        ax.grid(axis='y', alpha=0.3)
        
        plt.tight_layout()
        return fig
    
    def plot_all_distributions(
        self,
        results: Dict[str, Tuple[BenchmarkResult, BenchmarkResult]],
        figsize: Tuple[int, int] = (14, 10)
    ) -> Optional[plt.Figure]:
        """
        Plot distributions for all benchmarks in a grid.
        
        Args:
            results: Results from run_all()
            figsize: Figure size
            
        Returns:
            matplotlib Figure object
        """
        if not HAS_MATPLOTLIB:
            print("matplotlib not available")
            return None
        
        n = len(results)
        cols = 3
        rows = (n + cols - 1) // cols
        
        fig, axes = plt.subplots(rows, cols, figsize=figsize)
        axes = axes.flatten() if n > 1 else [axes]
        
        for idx, (name, (verified, stock)) in enumerate(results.items()):
            ax = axes[idx]
            
            data = [verified.times, stock.times]
            bp = ax.boxplot(data, positions=[1, 2], widths=0.5, patch_artist=True)
            
            bp['boxes'][0].set_facecolor('#2ecc71')
            bp['boxes'][1].set_facecolor('#3498db')
            
            ax.set_xticklabels(['Verified', 'Stock'])
            ax.set_ylabel('Time (ms)')
            ax.set_title(name)
            ax.grid(axis='y', alpha=0.3)
        
        # Hide unused subplots
        for idx in range(n, len(axes)):
            axes[idx].set_visible(False)
        
        plt.suptitle('Run Time Distributions', fontsize=14, y=1.02)
        plt.tight_layout()
        return fig
    
    def generate_report(
        self,
        results: Dict[str, Tuple[BenchmarkResult, BenchmarkResult]],
        output_dir: Optional[str] = None
    ) -> str:
        """
        Generate a markdown report with all results.
        
        Args:
            results: Results from run_all()
            output_dir: Directory to save plots (None = don't save)
            
        Returns:
            Markdown string with report
        """
        report = []
        report.append("# OCaml GC Benchmark Report\n")
        report.append(f"**Verified OCaml**: `{self.verified_ocaml}`\n")
        report.append(f"**Stock OCaml**: `{self.stock_ocaml}`\n\n")
        
        report.append("## Summary\n")
        report.append("| Benchmark | Verified (ms) | Stock (ms) | Speedup |")
        report.append("|-----------|---------------|------------|---------|")
        
        for name, (verified, stock) in results.items():
            speedup = stock.mean / verified.mean if verified.mean > 0 else 0
            winner = "✅" if speedup >= 1 else ""
            report.append(
                f"| {name} | {verified.mean:.2f} ± {verified.std:.2f} | "
                f"{stock.mean:.2f} ± {stock.std:.2f} | {speedup:.2f}x {winner} |"
            )
        
        report.append("\n## Detailed Results\n")
        
        for name, (verified, stock) in results.items():
            config = next((c for c in self.DEFAULT_BENCHMARKS if c.name == name), None)
            desc = config.description if config else ""
            
            report.append(f"### {name}\n")
            report.append(f"{desc}\n")
            report.append(f"- **Verified GC**: {verified.mean:.2f} ± {verified.std:.2f} ms "
                         f"(min: {verified.min:.2f}, max: {verified.max:.2f})")
            report.append(f"- **Stock OCaml**: {stock.mean:.2f} ± {stock.std:.2f} ms "
                         f"(min: {stock.min:.2f}, max: {stock.max:.2f})")
            report.append("")
        
        if output_dir and HAS_MATPLOTLIB:
            output_path = Path(output_dir)
            output_path.mkdir(exist_ok=True)
            
            # Save plots
            fig = self.plot_comparison(results)
            if fig:
                fig.savefig(output_path / "comparison.png", dpi=150)
                plt.close(fig)
            
            fig = self.plot_speedup(results)
            if fig:
                fig.savefig(output_path / "speedup.png", dpi=150)
                plt.close(fig)
            
            fig = self.plot_all_distributions(results)
            if fig:
                fig.savefig(output_path / "distributions.png", dpi=150)
                plt.close(fig)
            
            report.append("## Plots\n")
            report.append("![Comparison](comparison.png)\n")
            report.append("![Speedup](speedup.png)\n")
            report.append("![Distributions](distributions.png)\n")
        
        return "\n".join(report)


# ============================================================================
# CLI interface
# ============================================================================

def main():
    """Command-line interface for running benchmarks."""
    import argparse
    
    parser = argparse.ArgumentParser(description="OCaml GC Benchmark Suite")
    parser.add_argument("--verified", help="Path to verified GC ocamlopt")
    parser.add_argument("--stock", help="Path to stock ocamlopt")
    parser.add_argument("--benchmarks", nargs="+", help="Benchmarks to run")
    parser.add_argument("--warmup", type=int, default=2, help="Warmup runs")
    parser.add_argument("--runs", type=int, default=5, help="Timed runs")
    parser.add_argument("--output", help="Output directory for report")
    
    args = parser.parse_args()
    
    suite = BenchmarkSuite(
        verified_ocaml=args.verified,
        stock_ocaml=args.stock
    )
    
    results = suite.run_all(
        benchmarks=args.benchmarks,
        warmup=args.warmup,
        runs=args.runs
    )
    
    if args.output:
        report = suite.generate_report(results, args.output)
        with open(Path(args.output) / "report.md", "w") as f:
            f.write(report)
        print(f"\nReport saved to {args.output}/report.md")
    else:
        report = suite.generate_report(results)
        print("\n" + report)


if __name__ == "__main__":
    main()
