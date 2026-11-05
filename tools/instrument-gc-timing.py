#!/usr/bin/env python3
"""tools/instrument-gc-timing.py <snapshot_in> <snapshot_out>: copy an extracted-C snapshot and add
timers around mark, collect (mark+sweep+coalesce) and the whole gen_gc call,
plus a rescan counter.  Results go to stderr at exit as one GCTIME line.
Applied identically to the before and after snapshots; measurement only."""
import shutil, sys, re
src, dst = sys.argv[1], sys.argv[2]
shutil.rmtree(dst, ignore_errors=True); shutil.copytree(src, dst)
p = dst + '/GC_Gen_Impl.c'; s = open(p).read()
def once(old, new):
    global s
    assert s.count(old) == 1, (old, s.count(old)); s = s.replace(old, new)
hdr = '''
#include <time.h>
#include <stdio.h>
static uint64_t tm_now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return (uint64_t)t.tv_sec*1000000000ULL+t.tv_nsec;}
static uint64_t tm_mark, tm_collect, tm_gengc, tm_ncoll, tm_nrescan;
__attribute__((destructor)) static void tm_report(void){
  fprintf(stderr,"GCTIME collections=%llu rescans=%llu mark_ms=%.3f collect_ms=%.3f gen_gc_ms=%.3f\\n",
    (unsigned long long)tm_ncoll,(unsigned long long)tm_nrescan,tm_mark/1e6,tm_collect/1e6,tm_gengc/1e6);}
'''
once('#include "internal/GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.h"\n',
     '#include "internal/GC_Gen_Base_GC_Spec_GC_Lib_Header_GC_Lib_Address.h"\n' + hdr)
# mark
m = re.search(r'\n(  )(mark_loop_bounded(_flagged)?\(heap, st(, ov)?\);)\n', s)
assert m and len(re.findall(r'\n  mark_loop_bounded(_flagged)?\(heap, st(, ov)?\);\n', s)) == 1
s = s.replace(m.group(0), '\n  { uint64_t _tm0 = tm_now(); %s tm_mark += tm_now() - _tm0; }\n' % m.group(2))
# collect (whichever entry gen_gc uses)
m = re.search(r'    uint64_t final_fp = (collect(_with_roots)?\(gh\.major, st, fp_val\));\n', s)
assert m
s = s.replace(m.group(0), '    uint64_t _tm1 = tm_now(); uint64_t final_fp = %s; tm_collect += tm_now() - _tm1; tm_ncoll++;\n' % m.group(1))
# rescans
once('void rescan_heap_impl(heap_t heap, gray_stack_rec st)\n{\n',
     'void rescan_heap_impl(heap_t heap, gray_stack_rec st)\n{\n  tm_nrescan++;\n')
# whole gen_gc: rename definition, add timed wrapper
sig = '''FStar_Pervasives_Native_tuple2__uint64_t_bool
gen_gc(
  gen_heap_t gh,
  uint64_t *roots,
  size_t nroots,
  uint64_t *fwd_arr,
  uint64_t *queue,
  uint64_t *slots,
  size_t nslots,
  gray_stack_rec st
)
{'''
once(sig, sig.replace('gen_gc(', 'gen_gc_untimed(', 1))
s += '\n' + sig + '''
  uint64_t _tm2 = tm_now();
  FStar_Pervasives_Native_tuple2__uint64_t_bool r = gen_gc_untimed(gh, roots, nroots, fwd_arr, queue, slots, nslots, st);
  tm_gengc += tm_now() - _tm2;
  return r;
}
'''
open(p, 'w').write(s)
print('instrumented', p)
