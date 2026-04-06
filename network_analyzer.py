"""
Network Reachability Analyzer

Build network topologies with a GUI and run DFS-based
bidirectional reachability analysis.
Generates C code, compiles, executes, and displays results.
"""

import csv
import json
import math
import os
import shutil
import signal
import subprocess
import sys
import threading
from collections import defaultdict

import tkinter as tk
from tkinter import ttk, messagebox, filedialog, simpledialog, scrolledtext

NODE_RADIUS = 20

COLORS = {
    'source_a':     '#3B82F6',
    'source_b':     '#EF4444',
    'intermediate': '#6B7280',
    'edge_atob':    '#3B82F6',
    'edge_btoa':    '#EF4444',
    'edge_both':    '#8B5CF6',
    'select':       '#F59E0B',
    'mandatory':    '#F59E0B',
    'canvas_bg':    '#F8FAFC',
    'grid':         '#E2E8F0',
}

DIRECTION_LABELS = {'atob': 'AB', 'btoa': 'BA', 'both': 'BI'}

MODE_LABELS = {
    'select':           'Select/Move',
    'add_node':         'Add Node (click on canvas)',
    'add_edge_atob':    'Edge(A->B): click source node',
    'add_edge_btoa':    'Edge(B->A): click source node',
    'add_edge_both':    'Edge(Both): click source node',
    'delete':           'Click node/edge to delete',
    'toggle_fail':      'Click node/edge to toggle failure target '
                        '(solid outline = target, dashed = excluded)',
    'toggle_mandatory': 'Click node/edge to toggle mandatory '
                        '(gold ring = must be on path)',
}


class Node:
    def __init__(self, name, x, y, role='intermediate',
                 failure_target=True, mandatory=False):
        self.name = name
        self.x = x
        self.y = y
        self.role = role
        self.failure_target = failure_target
        self.mandatory = mandatory


class Edge:
    _counter = 0

    def __init__(self, src, dst, direction='atob',
                 failure_target=True, mandatory=False):
        Edge._counter += 1
        self.eid = Edge._counter
        self.src = src
        self.dst = dst
        self.direction = direction
        self.failure_target = failure_target
        self.mandatory = mandatory


class NetworkModel:
    def __init__(self):
        self.nodes = {}
        self.edges = []

    def add_node(self, name, x, y, role='intermediate',
                 failure_target=True, mandatory=False):
        if name in self.nodes:
            return False
        self.nodes[name] = Node(name, x, y, role, failure_target, mandatory)
        return True

    def remove_node(self, name):
        if name not in self.nodes:
            return
        self.edges = [e for e in self.edges if e.src != name and e.dst != name]
        del self.nodes[name]

    def add_edge(self, src, dst, direction='atob',
                 failure_target=True, mandatory=False):
        if src not in self.nodes or dst not in self.nodes or src == dst:
            return False
        for e in self.edges:
            if e.src == src and e.dst == dst and e.direction == direction:
                return False
        self.edges.append(Edge(src, dst, direction, failure_target, mandatory))
        return True

    def remove_edge(self, eid):
        self.edges = [e for e in self.edges if e.eid != eid]

    def clear(self):
        self.nodes.clear()
        self.edges.clear()

    def to_dict(self):
        return {
            'nodes': [
                {
                    'name': node.name, 'x': node.x, 'y': node.y,
                    'role': node.role, 'failure_target': node.failure_target,
                    'mandatory': node.mandatory,
                }
                for node in self.nodes.values()
            ],
            'edges': [
                {
                    'src': edge.src, 'dst': edge.dst,
                    'direction': edge.direction,
                    'failure_target': edge.failure_target,
                    'mandatory': edge.mandatory,
                }
                for edge in self.edges
            ],
        }

    def from_dict(self, data):
        self.clear()
        for n in data.get('nodes', []):
            self.add_node(
                n['name'], n['x'], n['y'],
                n.get('role', 'intermediate'),
                n.get('failure_target', True),
                n.get('mandatory', False),
            )
        for e in data.get('edges', []):
            self.add_edge(
                e['src'], e['dst'],
                e.get('direction', 'atob'),
                e.get('failure_target', True),
                e.get('mandatory', False),
            )


class CCodeGenerator:
    C_TEMPLATE_DFS_AND_UTILS = r"""
static inline int popcount(long p) { return __builtin_popcountl(p); }

static bool dfs(const bool fn[NUM_NODES], const bool fe[],
                int start, const int goals[], int ng,
                int edge_list[][NUM_NODES][MAX_PARALLEL],
                int edge_cnt[][NUM_NODES]) {
    if (fn[start]) return false;
    bool vis[NUM_NODES] = {false};
    bool in_stk[NUM_NODES] = {false};
    int stk[NUM_NODES], sp = 0;
    stk[sp++] = start;
    in_stk[start] = true;
    while (sp > 0) {
        int c = stk[--sp];
        if (vis[c] || fn[c]) continue;
        vis[c] = true;
        for (int g = 0; g < ng; g++)
            if (c == goals[g]) return true;
        for (int i = 0; i < NUM_NODES; i++) {
            if (fn[i] || vis[i] || in_stk[i] || edge_cnt[c][i] == 0) continue;
            bool ok = false;
            for (int k = 0; k < edge_cnt[c][i]; k++)
                if (!fe[edge_list[c][i][k]]) { ok = true; break; }
            if (ok) { stk[sp++] = i; in_stk[i] = true; }
        }
    }
    return false;
}

#define dfs_atob(fn,fe,start,goals,ng) dfs(fn,fe,start,goals,ng,atob_edge_list,atob_edge_cnt)
#define dfs_btoa(fn,fe,start,goals,ng) dfs(fn,fe,start,goals,ng,btoa_edge_list,btoa_edge_cnt)

static bool reachable_AtoB(const bool fn[], const bool fe[]) {
    bool found = false;
    for (int i = 0; i < NUM_SA; i++)
        if (dfs_atob(fn, fe, source_a[i], source_b, NUM_SB)) { found = true; break; }
    if (!found) return false;

    for (int j = 0; j < NUM_MAND_NODES; j++) {
        int m = mand_node_idx[j];
        if (fn[m]) return false;
        bool ok = false;
        for (int i = 0; i < NUM_SA; i++)
            if (dfs_atob(fn, fe, source_a[i], (int[]){m}, 1)) { ok = true; break; }
        if (!ok) return false;
        if (!dfs_atob(fn, fe, m, source_b, NUM_SB)) return false;
    }

    for (int j = 0; j < NUM_MAND_EDGES_AB; j++) {
        if (fe[mand_ea_eidx[j]]) return false;
        int u = mand_ea_src[j], v = mand_ea_dst[j];
        bool ok = false;
        for (int i = 0; i < NUM_SA; i++)
            if (dfs_atob(fn, fe, source_a[i], (int[]){u}, 1)) { ok = true; break; }
        if (!ok) return false;
        if (!dfs_atob(fn, fe, v, source_b, NUM_SB)) return false;
    }
    return true;
}

static bool reachable_BtoA(const bool fn[], const bool fe[]) {
    bool found = false;
    for (int i = 0; i < NUM_SB; i++)
        if (dfs_btoa(fn, fe, source_b[i], source_a, NUM_SA)) { found = true; break; }
    if (!found) return false;

    for (int j = 0; j < NUM_MAND_NODES; j++) {
        int m = mand_node_idx[j];
        if (fn[m]) return false;
        bool ok = false;
        for (int i = 0; i < NUM_SB; i++)
            if (dfs_btoa(fn, fe, source_b[i], (int[]){m}, 1)) { ok = true; break; }
        if (!ok) return false;
        if (!dfs_btoa(fn, fe, m, source_a, NUM_SA)) return false;
    }

    for (int j = 0; j < NUM_MAND_EDGES_BA; j++) {
        if (fe[mand_eb_eidx[j]]) return false;
        int u = mand_eb_src[j], v = mand_eb_dst[j];
        bool ok = false;
        for (int i = 0; i < NUM_SB; i++)
            if (dfs_btoa(fn, fe, source_b[i], (int[]){u}, 1)) { ok = true; break; }
        if (!ok) return false;
        if (!dfs_btoa(fn, fe, v, source_a, NUM_SA)) return false;
    }
    return true;
}

static void set_fail(long p, bool fn[NUM_NODES], bool fe[]) {
    memset(fn, 0, NUM_NODES * sizeof(bool));
    memset(fe, 0, NUM_EDGES * sizeof(bool));
    for (int i = 0; i < NUM_FAIL_NODES; i++) fn[fail_node_idx[i]] = (p >> i) & 1;
    for (int i = 0; i < NUM_FAIL_EDGES; i++) fe[fail_edge_idx[i]] = (p >> (NUM_FAIL_NODES + i)) & 1;
}

static void csv_hdr(FILE *fp) {
    fprintf(fp, "failure_count");
    for (int i = 0; i < NUM_NODES; i++) fprintf(fp, ",%s", node_names[i]);
    for (int i = 0; i < NUM_EDGES; i++) fprintf(fp, ",%s", edge_names[i]);
    fprintf(fp, "\n");
}

static void csv_row(FILE *fp, int fc, const bool fn[NUM_NODES], const bool fe[]) {
    fprintf(fp, "%d", fc);
    for (int i = 0; i < NUM_NODES; i++) fprintf(fp, ",%s", fn[i] ? "F" : "T");
    for (int i = 0; i < NUM_EDGES; i++) fprintf(fp, ",%s", fe[i] ? "F" : "T");
    fprintf(fp, "\n");
}

static FILE *next_csv(const char *base, int num, char *buf, size_t len) {
    snprintf(buf, len, "%s_%d.csv", base, num);
    FILE *fp = fopen(buf, "w");
    if (fp) csv_hdr(fp);
    return fp;
}
"""

    C_TEMPLATE_MAIN = r"""
int main(int argc, char *argv[]) {
    const char *base = (argc >= 2) ? argv[1] : "{default_base}";
    init_adjacency();

    bool fn[NUM_NODES];
    bool fe[NUM_EDGES + 1];
    memset(fe, 0, sizeof(fe));

    int file_count = 1;
    long rows = 0, total = 0;
    char buf[256];
    long unreachable_per_tc[NUM_COMPONENTS + 1];
    long total_per_tc[NUM_COMPONENTS + 1];
    memset(unreachable_per_tc, 0, sizeof(unreachable_per_tc));
    memset(total_per_tc, 0, sizeof(total_per_tc));

    FILE *fp = next_csv(base, file_count, buf, sizeof(buf));
    if (!fp) { fprintf(stderr, "Cannot open\n"); return 1; }

    for (int tc = 0; tc <= NUM_COMPONENTS; tc++) {
        long cnt = 0, tc_total = 0;
        for (long p = 0; p < MAX_PATTERNS; p++) {
            if (popcount(p) != tc) continue;
            tc_total++;
            set_fail(p, fn, fe);
            if (reachable_AtoB(fn, fe)) continue;
            if (reachable_BtoA(fn, fe)) continue;
            csv_row(fp, tc, fn, fe);
            rows++;
            cnt++;
            if (rows >= MAX_DATA_ROWS) {
                fclose(fp);
                file_count++;
                fp = next_csv(base, file_count, buf, sizeof(buf));
                if (!fp) { fprintf(stderr, "Cannot open\n"); return 1; }
                rows = 0;
            }
        }
        unreachable_per_tc[tc] = cnt;
        total_per_tc[tc] = tc_total;
        printf("Failures %2d: unreachable=%ld  reachable=%ld  total=%ld\n",
               tc, cnt, tc_total - cnt, tc_total);
        total += cnt;
    }
    fclose(fp);

    char sum_fn[256];
    snprintf(sum_fn, sizeof(sum_fn), "%s_summary.csv", base);
    FILE *sfp = fopen(sum_fn, "w");
    if (!sfp) { fprintf(stderr, "Cannot open summary\n"); return 1; }
    fprintf(sfp, "failure_count,unreachable_count,reachable_count,"
                 "total_count,arrival_rate\n");
    for (int tc = 0; tc <= NUM_COMPONENTS; tc++) {
        long reach = total_per_tc[tc] - unreachable_per_tc[tc];
        double rate = total_per_tc[tc] > 0
                      ? (double)reach / total_per_tc[tc] : 0.0;
        fprintf(sfp, "%d,%ld,%ld,%ld,%.6f\n",
                tc, unreachable_per_tc[tc], reach, total_per_tc[tc], rate);
    }
    fclose(sfp);

    printf("-----------------------------\n");
    printf("Total unreachable: %ld patterns / %d detail files\n",
           total, file_count);
    printf("Summary: %s\n", sum_fn);
    return 0;
}
"""

    def generate(self, model, output_base='result', max_rows=1000000):
        nodes = list(model.nodes.values())
        edges = list(model.edges)
        num_nodes = len(nodes)
        num_edges = len(edges)

        node_index = {node.name: i for i, node in enumerate(nodes)}
        edge_index = {edge.eid: i for i, edge in enumerate(edges)}

        source_a_indices = [node_index[n.name] for n in nodes if n.role == 'source_a']
        source_b_indices = [node_index[n.name] for n in nodes if n.role == 'source_b']

        fail_node_indices = [i for i, n in enumerate(nodes) if n.failure_target]
        fail_edge_indices = [i for i, e in enumerate(edges) if e.failure_target]

        mand_node_indices = [i for i, n in enumerate(nodes) if n.mandatory]
        mand_edges_ab = [
            (edge_index[e.eid], node_index[e.src], node_index[e.dst])
            for e in edges if e.mandatory and e.direction in ('atob', 'both')
        ]
        mand_edges_ba = [
            (edge_index[e.eid], node_index[e.src], node_index[e.dst])
            for e in edges if e.mandatory and e.direction in ('btoa', 'both')
        ]

        atob_adj = defaultdict(list)
        btoa_adj = defaultdict(list)
        for edge in edges:
            src, dst = node_index[edge.src], node_index[edge.dst]
            eidx = edge_index[edge.eid]
            if edge.direction in ('atob', 'both'):
                atob_adj[(src, dst)].append(eidx)
            if edge.direction == 'btoa':
                btoa_adj[(src, dst)].append(eidx)
            if edge.direction == 'both':
                btoa_adj[(dst, src)].append(eidx)

        lines = []
        lines.append(self._emit_headers(
            num_nodes, num_edges, len(fail_node_indices), len(fail_edge_indices),
            max_rows, len(mand_node_indices), len(mand_edges_ab), len(mand_edges_ba),
        ))
        lines.append(self._emit_node_defines(nodes, node_index))
        lines.append(self._emit_sources(source_a_indices, source_b_indices))
        lines.append(self._emit_fail_indices(fail_node_indices, fail_edge_indices))
        lines.append(self._emit_mandatory_arrays(
            mand_node_indices, mand_edges_ab, mand_edges_ba,
        ))
        lines.append(self._emit_name_tables(nodes, edges, node_index))
        lines.append(self._emit_adjacency(atob_adj, btoa_adj))
        lines.append(self.C_TEMPLATE_DFS_AND_UTILS)

        escaped_base = output_base.replace('\\', '\\\\').replace('"', '\\"')
        lines.append(self.C_TEMPLATE_MAIN.replace('{default_base}', escaped_base))

        return '\n'.join(lines)

    @staticmethod
    def _int_list(values):
        return ','.join(str(v) for v in values)

    @staticmethod
    def _sanitize_name(name):
        return name.replace('-', '_').replace(' ', '_')

    @staticmethod
    def _edge_label(edge):
        direction_tag = DIRECTION_LABELS[edge.direction]
        return f"{edge.src}-{edge.dst}-{direction_tag}"

    def _emit_headers(self, num_nodes, num_edges, num_fail_nodes, num_fail_edges,
                      max_rows, num_mand_nodes, num_mand_edges_ab, num_mand_edges_ba):
        return (
            '#include <stdio.h>\n'
            '#include <stdlib.h>\n'
            '#include <string.h>\n'
            '#include <stdbool.h>\n'
            '\n'
            f'#define NUM_NODES          {num_nodes}\n'
            f'#define NUM_EDGES          {num_edges}\n'
            f'#define NUM_FAIL_NODES     {num_fail_nodes}\n'
            f'#define NUM_FAIL_EDGES     {num_fail_edges}\n'
            f'#define NUM_COMPONENTS     (NUM_FAIL_NODES + NUM_FAIL_EDGES)\n'
            f'#define MAX_PATTERNS       (1L << NUM_COMPONENTS)\n'
            f'#define MAX_DATA_ROWS      {max_rows}\n'
            f'#define MAX_PARALLEL       2\n'
            f'#define NUM_MAND_NODES     {num_mand_nodes}\n'
            f'#define NUM_MAND_EDGES_AB  {num_mand_edges_ab}\n'
            f'#define NUM_MAND_EDGES_BA  {num_mand_edges_ba}\n'
        )

    def _emit_node_defines(self, nodes, node_index):
        lines = [
            f'#define NODE_{self._sanitize_name(node.name)} {node_index[node.name]}'
            for node in nodes
        ]
        return '\n'.join(lines) + '\n'

    def _emit_sources(self, source_a, source_b):
        return (
            f'static const int source_a[] = {{{self._int_list(source_a)}}};\n'
            f'#define NUM_SA {len(source_a)}\n'
            f'static const int source_b[] = {{{self._int_list(source_b)}}};\n'
            f'#define NUM_SB {len(source_b)}\n'
        )

    def _emit_fail_indices(self, fail_nodes, fail_edges):
        return (
            f'static const int fail_node_idx[NUM_FAIL_NODES+1] = '
            f'{{{self._int_list(fail_nodes)}}};\n'
            f'static const int fail_edge_idx[NUM_FAIL_EDGES+1] = '
            f'{{{self._int_list(fail_edges)}}};\n'
        )

    def _emit_mandatory_arrays(self, mand_nodes, mand_edges_ab, mand_edges_ba):
        lines = [
            f'static const int mand_node_idx[NUM_MAND_NODES+1] = '
            f'{{{self._int_list(mand_nodes)}}};\n'
        ]
        lines.append(self._emit_mandatory_edge_group(
            'ea', 'NUM_MAND_EDGES_AB', mand_edges_ab,
        ))
        lines.append(self._emit_mandatory_edge_group(
            'eb', 'NUM_MAND_EDGES_BA', mand_edges_ba,
        ))
        return '\n'.join(lines)

    def _emit_mandatory_edge_group(self, prefix, size_macro, edges):
        if edges:
            eidx = self._int_list(e[0] for e in edges)
            srcs = self._int_list(e[1] for e in edges)
            dsts = self._int_list(e[2] for e in edges)
            return (
                f'static const int mand_{prefix}_eidx[{size_macro}+1] = {{{eidx}}};\n'
                f'static const int mand_{prefix}_src [{size_macro}+1] = {{{srcs}}};\n'
                f'static const int mand_{prefix}_dst [{size_macro}+1] = {{{dsts}}};\n'
            )
        return (
            f'static const int mand_{prefix}_eidx[1] = {{0}}, '
            f'mand_{prefix}_src[1] = {{0}}, '
            f'mand_{prefix}_dst[1] = {{0}};\n'
        )

    def _emit_name_tables(self, nodes, edges, node_index):
        node_entries = '\n'.join(
            f'    [{node_index[node.name]}] = "{node.name}",'
            for node in nodes
        )
        lines = [f'static const char *node_names[NUM_NODES] = {{\n{node_entries}\n}};\n']

        if edges:
            edge_entries = '\n'.join(
                f'    [{i}] = "{self._edge_label(edge)}",'
                for i, edge in enumerate(edges)
            )
            lines.append(
                f'static const char *edge_names[NUM_EDGES] = {{\n{edge_entries}\n}};\n'
            )
        else:
            lines.append('static const char *edge_names[1] = {""};\n')

        return '\n'.join(lines)

    def _emit_adjacency(self, atob_adj, btoa_adj):
        lines = [
            'static int atob_edge_list[NUM_NODES][NUM_NODES][MAX_PARALLEL];',
            'static int atob_edge_cnt [NUM_NODES][NUM_NODES];',
            'static int btoa_edge_list[NUM_NODES][NUM_NODES][MAX_PARALLEL];',
            'static int btoa_edge_cnt [NUM_NODES][NUM_NODES];',
            '',
            'static void init_adjacency(void) {',
            '    memset(atob_edge_list, -1, sizeof(atob_edge_list));',
            '    memset(atob_edge_cnt,   0, sizeof(atob_edge_cnt));',
            '    memset(btoa_edge_list, -1, sizeof(btoa_edge_list));',
            '    memset(btoa_edge_cnt,   0, sizeof(btoa_edge_cnt));',
        ]
        for (src, dst), edge_indices in atob_adj.items():
            for eidx in edge_indices:
                lines.append(
                    f'    if(atob_edge_cnt[{src}][{dst}] < MAX_PARALLEL) '
                    f'atob_edge_list[{src}][{dst}]'
                    f'[atob_edge_cnt[{src}][{dst}]++] = {eidx};'
                )
        for (src, dst), edge_indices in btoa_adj.items():
            for eidx in edge_indices:
                lines.append(
                    f'    if(btoa_edge_cnt[{src}][{dst}] < MAX_PARALLEL) '
                    f'btoa_edge_list[{src}][{dst}]'
                    f'[btoa_edge_cnt[{src}][{dst}]++] = {eidx};'
                )
        lines.append('}')
        return '\n'.join(lines) + '\n'


def make_preset_24():
    node_defs = [
        ('A1',              80,  180, 'source_a'),
        ('A2',              80,  520, 'source_a'),
        ('ERP1_1',         380,  150, 'intermediate'),
        ('ERP1_2',         660,  100, 'intermediate'),
        ('ERP1_3',         660,  230, 'intermediate'),
        ('ERP2_1',         380,  550, 'intermediate'),
        ('ERP2_2',         660,  470, 'intermediate'),
        ('ERP2_3',         660,  600, 'intermediate'),
        ('B1',            1050,  180, 'source_b'),
        ('B2',            1050,  520, 'source_b'),
        ('L_A1_ERP1_1',    220,  120, 'intermediate'),
        ('L_A1_ERP2_1',    220,  310, 'intermediate'),
        ('L_A2_ERP1_1',    220,  390, 'intermediate'),
        ('L_A2_ERP2_1',    220,  580, 'intermediate'),
        ('L_ERP1_1_ERP1_2', 520, 100, 'intermediate'),
        ('L_ERP1_1_ERP1_3', 520, 210, 'intermediate'),
        ('L_ERP1_2_B1',    830,  100, 'intermediate'),
        ('L_ERP1_3_ERP1_2', 580, 170, 'intermediate'),
        ('L_ERP2_1_ERP2_2', 520, 490, 'intermediate'),
        ('L_ERP2_1_ERP2_3', 520, 590, 'intermediate'),
        ('L_ERP2_2_B2',    830,  470, 'intermediate'),
        ('L_ERP2_3_ERP2_2', 580, 540, 'intermediate'),
        ('L_ERP1_2_B2',    870,  310, 'intermediate'),
        ('L_ERP2_2_B1',    870,  380, 'intermediate'),
    ]

    atob_edges = [
        ('A1', 'L_A1_ERP1_1'),       ('L_A1_ERP1_1', 'ERP1_1'),
        ('A1', 'L_A1_ERP2_1'),       ('L_A1_ERP2_1', 'ERP2_1'),
        ('A2', 'L_A2_ERP1_1'),       ('L_A2_ERP1_1', 'ERP1_1'),
        ('A2', 'L_A2_ERP2_1'),       ('L_A2_ERP2_1', 'ERP2_1'),
        ('ERP1_1', 'L_ERP1_1_ERP1_2'), ('L_ERP1_1_ERP1_2', 'ERP1_2'),
        ('ERP1_1', 'L_ERP1_1_ERP1_3'), ('L_ERP1_1_ERP1_3', 'ERP1_3'),
        ('ERP1_2', 'L_ERP1_2_B1'),   ('L_ERP1_2_B1', 'B1'),
        ('ERP1_3', 'L_ERP1_3_ERP1_2'), ('L_ERP1_3_ERP1_2', 'ERP1_2'),
        ('ERP2_1', 'L_ERP2_1_ERP2_2'), ('L_ERP2_1_ERP2_2', 'ERP2_2'),
        ('ERP2_1', 'L_ERP2_1_ERP2_3'), ('L_ERP2_1_ERP2_3', 'ERP2_3'),
        ('ERP2_2', 'L_ERP2_2_B2'),   ('L_ERP2_2_B2', 'B2'),
        ('ERP2_3', 'L_ERP2_3_ERP2_2'), ('L_ERP2_3_ERP2_2', 'ERP2_2'),
        ('ERP1_2', 'L_ERP1_2_B2'),   ('L_ERP1_2_B2', 'B2'),
        ('ERP2_2', 'L_ERP2_2_B1'),   ('L_ERP2_2_B1', 'B1'),
    ]

    btoa_edges = [
        ('B1', 'L_ERP1_2_B1'),       ('L_ERP1_2_B1', 'ERP1_2'),
        ('B2', 'L_ERP2_2_B2'),       ('L_ERP2_2_B2', 'ERP2_2'),
        ('ERP1_2', 'L_ERP1_1_ERP1_2'), ('L_ERP1_1_ERP1_2', 'ERP1_1'),
        ('ERP1_2', 'L_ERP1_3_ERP1_2'), ('L_ERP1_3_ERP1_2', 'ERP1_3'),
        ('ERP1_3', 'L_ERP1_1_ERP1_3'), ('L_ERP1_1_ERP1_3', 'ERP1_1'),
        ('ERP1_1', 'L_A1_ERP1_1'),   ('L_A1_ERP1_1', 'A1'),
        ('ERP1_1', 'L_A2_ERP1_1'),   ('L_A2_ERP1_1', 'A2'),
        ('ERP2_2', 'L_ERP2_1_ERP2_2'), ('L_ERP2_1_ERP2_2', 'ERP2_1'),
        ('ERP2_2', 'L_ERP2_3_ERP2_2'), ('L_ERP2_3_ERP2_2', 'ERP2_3'),
        ('ERP2_3', 'L_ERP2_1_ERP2_3'), ('L_ERP2_1_ERP2_3', 'ERP2_1'),
        ('ERP2_1', 'L_A1_ERP2_1'),   ('L_A1_ERP2_1', 'A1'),
        ('ERP2_1', 'L_A2_ERP2_1'),   ('L_A2_ERP2_1', 'A2'),
        ('B2', 'L_ERP1_2_B2'),       ('L_ERP1_2_B2', 'ERP1_2'),
        ('B1', 'L_ERP2_2_B1'),       ('L_ERP2_2_B1', 'ERP2_2'),
    ]

    data = {
        'nodes': [
            {'name': name, 'x': x, 'y': y, 'role': role}
            for name, x, y, role in node_defs
        ],
        'edges': (
            [{'src': s, 'dst': d, 'direction': 'atob'} for s, d in atob_edges]
            + [{'src': s, 'dst': d, 'direction': 'btoa'} for s, d in btoa_edges]
        ),
    }
    return data


class App:
    def __init__(self, root):
        self.root = root
        self.root.title("Network Reachability Analyzer")
        self.root.geometry("1280x820")
        self.model = NetworkModel()
        self.mode = 'select'
        self.selected = None
        self.edge_src = None
        self.dragging = None
        self.drag_offset = (0, 0)
        self.canvas_ids = {}
        self.node_items = {}
        self.edge_items = {}
        self.edge_offsets = {}
        self._build_ui()

    # ── UI construction ──

    def _build_ui(self):
        self._build_toolbar()
        self._build_canvas_and_results()
        self._build_statusbar()
        self._bind_events()

    def _build_toolbar(self):
        toolbar = ttk.Frame(self.root)
        toolbar.pack(fill=tk.X, padx=4, pady=2)

        ttk.Label(toolbar, text="Mode:").pack(side=tk.LEFT, padx=(4, 2))
        self.mode_var = tk.StringVar(value='select')
        modes = [
            ('Select/Move', 'select'),
            ('Add Node', 'add_node'),
            ('Edge(A->B)', 'add_edge_atob'),
            ('Edge(B->A)', 'add_edge_btoa'),
            ('Edge(Both)', 'add_edge_both'),
            ('Delete', 'delete'),
            ('Toggle Fail', 'toggle_fail'),
            ('Toggle Mandatory', 'toggle_mandatory'),
        ]
        for text, value in modes:
            ttk.Radiobutton(
                toolbar, text=text, variable=self.mode_var,
                value=value, command=self._mode_changed,
            ).pack(side=tk.LEFT, padx=2)

        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(
            side=tk.LEFT, fill=tk.Y, padx=6,
        )
        ttk.Label(toolbar, text="Node Role:").pack(side=tk.LEFT, padx=2)
        self.role_var = tk.StringVar(value='intermediate')
        for text, value in [('Source A', 'source_a'), ('Source B', 'source_b'),
                            ('Intermediate', 'intermediate')]:
            ttk.Radiobutton(
                toolbar, text=text, variable=self.role_var, value=value,
            ).pack(side=tk.LEFT, padx=1)

        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(
            side=tk.LEFT, fill=tk.Y, padx=6,
        )
        buttons = [
            ("Run Analysis", self._run_analysis),
            ("Reliability",  self._run_reliability),
            ("Export C",     self._export_c),
            ("Save",         self._save),
            ("Load",         self._load),
            ("Preset",       self._load_preset),
            ("Clear",        self._clear),
        ]
        for text, command in buttons:
            ttk.Button(toolbar, text=text, command=command).pack(
                side=tk.LEFT, padx=2,
            )

    def _build_canvas_and_results(self):
        paned = ttk.PanedWindow(self.root, orient=tk.VERTICAL)
        paned.pack(fill=tk.BOTH, expand=True, padx=4, pady=2)

        canvas_frame = ttk.Frame(paned)
        self.canvas = tk.Canvas(
            canvas_frame, bg=COLORS['canvas_bg'],
            width=1200, height=500, scrollregion=(0, 0, 2000, 1200),
        )
        scrollbar_x = ttk.Scrollbar(
            canvas_frame, orient=tk.HORIZONTAL, command=self.canvas.xview,
        )
        scrollbar_y = ttk.Scrollbar(
            canvas_frame, orient=tk.VERTICAL, command=self.canvas.yview,
        )
        self.canvas.configure(
            xscrollcommand=scrollbar_x.set, yscrollcommand=scrollbar_y.set,
        )
        scrollbar_y.pack(side=tk.RIGHT, fill=tk.Y)
        scrollbar_x.pack(side=tk.BOTTOM, fill=tk.X)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        paned.add(canvas_frame, weight=3)

        result_frame = ttk.LabelFrame(paned, text="Analysis Results")
        self.result_text = scrolledtext.ScrolledText(
            result_frame, height=10, font=('Consolas', 10),
        )
        self.result_text.pack(fill=tk.BOTH, expand=True)
        paned.add(result_frame, weight=1)

        self._draw_grid()

    def _build_statusbar(self):
        self.status_var = tk.StringVar(value="Mode: Select/Move")
        ttk.Label(
            self.root, textvariable=self.status_var,
            relief=tk.SUNKEN, anchor=tk.W,
        ).pack(fill=tk.X, side=tk.BOTTOM)

    def _bind_events(self):
        self.canvas.bind('<Button-1>', self._on_click)
        self.canvas.bind('<B1-Motion>', self._on_drag)
        self.canvas.bind('<ButtonRelease-1>', self._on_release)
        self.root.bind('<Delete>', self._on_delete_key)
        self.root.bind('<Escape>', self._on_escape)

    # ── Drawing ──

    def _draw_grid(self):
        for x in range(0, 2001, 50):
            self.canvas.create_line(x, 0, x, 1200, fill=COLORS['grid'], tags='grid')
        for y in range(0, 1201, 50):
            self.canvas.create_line(0, y, 2000, y, fill=COLORS['grid'], tags='grid')

    def _redraw(self):
        self.canvas.delete('dynamic')
        self.canvas_ids.clear()
        self.node_items.clear()
        self.edge_items.clear()
        self.edge_offsets = self._compute_edge_offsets()

        for edge in self.model.edges:
            self._draw_edge(edge, self.edge_offsets.get(edge.eid, 0))
        for node in self.model.nodes.values():
            self._draw_node(node)

        if self.edge_src and self.edge_src in self.model.nodes:
            node = self.model.nodes[self.edge_src]
            r = NODE_RADIUS
            self.canvas.create_oval(
                node.x - r - 4, node.y - r - 4,
                node.x + r + 4, node.y + r + 4,
                outline=COLORS['select'], width=3, dash=(4, 2), tags='dynamic',
            )

    def _draw_node(self, node):
        x, y, r = node.x, node.y, NODE_RADIUS
        fill_color = COLORS.get(node.role, COLORS['intermediate'])
        is_selected = (self.selected == ('node', node.name))
        outline_width = 3 if is_selected else 1.5
        outline_color = COLORS['select'] if is_selected else '#1E293B'
        dash = (5, 4) if not node.failure_target else ()

        circle_id = self.canvas.create_oval(
            x - r, y - r, x + r, y + r,
            fill=fill_color, outline=outline_color,
            width=outline_width, dash=dash, tags='dynamic',
        )
        self.canvas_ids[circle_id] = ('node', node.name)

        font_size = 8 if len(node.name) > 6 else 9
        text_id = self.canvas.create_text(
            x, y + r + 10, text=node.name,
            font=('Arial', font_size), fill='#1E293B', anchor=tk.N, tags='dynamic',
        )
        self.canvas_ids[text_id] = ('node', node.name)
        items = [circle_id, text_id]

        if node.role != 'intermediate':
            badge = 'A' if node.role == 'source_a' else 'B'
            badge_id = self.canvas.create_text(
                x, y, text=badge, fill='white',
                font=('Arial', 10, 'bold'), tags='dynamic',
            )
            items.append(badge_id)

        if not node.failure_target:
            x_mark_id = self.canvas.create_text(
                x + r - 4, y - r + 4, text='x', fill='white',
                font=('Arial', 7, 'bold'), tags='dynamic',
            )
            items.append(x_mark_id)

        if node.mandatory:
            ring_id = self.canvas.create_oval(
                x - r - 5, y - r - 5, x + r + 5, y + r + 5,
                outline=COLORS['mandatory'], width=2.5, tags='dynamic',
            )
            m_label_id = self.canvas.create_text(
                x + r + 1, y - r - 1, text='M',
                fill=COLORS['mandatory'], font=('Arial', 7, 'bold'), tags='dynamic',
            )
            items += [ring_id, m_label_id]

        self.node_items[node.name] = items

    def _compute_edge_offsets(self):
        groups = {}
        for edge in self.model.edges:
            key = (min(edge.src, edge.dst), max(edge.src, edge.dst))
            groups.setdefault(key, []).append(edge)

        offsets = {}
        for group in groups.values():
            count = len(group)
            for i, edge in enumerate(group):
                offsets[edge.eid] = (i - (count - 1) / 2) * 8 if count > 1 else 0
        return offsets

    def _calc_edge_coords(self, edge, offset):
        if edge.src not in self.model.nodes or edge.dst not in self.model.nodes:
            return None
        src_node = self.model.nodes[edge.src]
        dst_node = self.model.nodes[edge.dst]

        dx = dst_node.x - src_node.x
        dy = dst_node.y - src_node.y
        dist = math.hypot(dx, dy)
        if dist < 1:
            return None

        ux, uy = dx / dist, dy / dist
        x1 = src_node.x + ux * NODE_RADIUS
        y1 = src_node.y + uy * NODE_RADIUS
        x2 = dst_node.x - ux * NODE_RADIUS
        y2 = dst_node.y - uy * NODE_RADIUS

        if offset != 0:
            perp_x, perp_y = -uy * offset, ux * offset
            x1 += perp_x
            y1 += perp_y
            x2 += perp_x
            y2 += perp_y

        return x1, y1, x2, y2

    def _draw_edge(self, edge, offset=0):
        coords = self._calc_edge_coords(edge, offset)
        if coords is None:
            return
        x1, y1, x2, y2 = coords

        color = COLORS.get(f'edge_{edge.direction}', COLORS['edge_atob'])
        is_selected = (self.selected == ('edge', edge.eid))
        width = 3 if is_selected else 1.5
        if is_selected:
            color = COLORS['select']
        dash = (8, 5) if not edge.failure_target else ()

        line_id = self.canvas.create_line(
            x1, y1, x2, y2, fill=color, width=width,
            arrow=tk.LAST, arrowshape=(10, 12, 5), dash=dash, tags='dynamic',
        )
        self.canvas_ids[line_id] = ('edge', edge.eid)
        self.edge_items[edge.eid] = line_id

        if edge.mandatory:
            mx, my = (x1 + x2) / 2, (y1 + y2) / 2
            diamond_r = 5
            diamond_id = self.canvas.create_polygon(
                mx, my - diamond_r, mx + diamond_r, my,
                mx, my + diamond_r, mx - diamond_r, my,
                fill=COLORS['mandatory'], outline='', tags='dynamic',
            )
            self.canvas_ids[diamond_id] = ('edge', edge.eid)

    def _update_edge_coords(self, edge):
        line_id = self.edge_items.get(edge.eid)
        if line_id is None:
            return
        coords = self._calc_edge_coords(edge, self.edge_offsets.get(edge.eid, 0))
        if coords is None:
            return
        self.canvas.coords(line_id, *coords)

    # ── Interaction ──

    def _find_item(self, x, y):
        items = self.canvas.find_overlapping(x - 5, y - 5, x + 5, y + 5)
        for item in reversed(items):
            if item in self.canvas_ids:
                return self.canvas_ids[item]
        return None

    def _mode_changed(self):
        self.mode = self.mode_var.get()
        self.edge_src = None
        self.status_var.set(f"Mode: {MODE_LABELS.get(self.mode, self.mode)}")
        self._redraw()

    def _on_click(self, event):
        x = self.canvas.canvasx(event.x)
        y = self.canvas.canvasy(event.y)
        item = self._find_item(x, y)

        handler = {
            'select':           self._click_select,
            'add_node':         self._click_add_node,
            'delete':           self._click_delete,
            'toggle_fail':      self._click_toggle_fail,
            'toggle_mandatory': self._click_toggle_mandatory,
        }.get(self.mode)

        if handler:
            handler(x, y, item)
        elif self.mode.startswith('add_edge'):
            self._click_add_edge(x, y, item)

    def _click_select(self, x, y, item):
        self.selected = item
        if item and item[0] == 'node':
            self.dragging = item[1]
            node = self.model.nodes[self.dragging]
            self.drag_offset = (x - node.x, y - node.y)
        self._redraw()

    def _click_add_node(self, x, y, item):
        name = simpledialog.askstring("Add Node", "Node name:", parent=self.root)
        if not name or not name.strip():
            return
        name = name.strip()
        if self.model.add_node(name, x, y, self.role_var.get()):
            self._redraw()
        else:
            messagebox.showwarning("Warning", f"Node '{name}' already exists")

    def _click_add_edge(self, x, y, item):
        if not item or item[0] != 'node':
            return
        if self.edge_src is None:
            self.edge_src = item[1]
            self.status_var.set(f"Source: {item[1]} -> click destination node")
            self._redraw()
        else:
            direction = self.mode.replace('add_edge_', '')
            if self.model.add_edge(self.edge_src, item[1], direction):
                self.edge_src = None
                self._mode_changed()
                self._redraw()
            else:
                messagebox.showwarning(
                    "Warning", "Cannot add edge (duplicate or self-loop)",
                )
                self.edge_src = None
                self._mode_changed()

    def _click_delete(self, x, y, item):
        if not item:
            return
        if item[0] == 'node':
            self.model.remove_node(item[1])
        elif item[0] == 'edge':
            self.model.remove_edge(item[1])
        self.selected = None
        self._redraw()

    def _click_toggle_fail(self, x, y, item):
        if not item:
            return
        if item[0] == 'node':
            self.model.nodes[item[1]].failure_target ^= True
        elif item[0] == 'edge':
            for edge in self.model.edges:
                if edge.eid == item[1]:
                    edge.failure_target ^= True
                    break
        self._redraw()

    def _click_toggle_mandatory(self, x, y, item):
        if not item:
            return
        if item[0] == 'node':
            self.model.nodes[item[1]].mandatory ^= True
        elif item[0] == 'edge':
            for edge in self.model.edges:
                if edge.eid == item[1]:
                    edge.mandatory ^= True
                    break
        self._redraw()

    def _on_drag(self, event):
        if self.mode != 'select' or not self.dragging:
            return
        node = self.model.nodes[self.dragging]
        new_x = self.canvas.canvasx(event.x) - self.drag_offset[0]
        new_y = self.canvas.canvasy(event.y) - self.drag_offset[1]
        dx, dy = new_x - node.x, new_y - node.y
        node.x, node.y = new_x, new_y

        for canvas_id in self.node_items.get(self.dragging, []):
            self.canvas.move(canvas_id, dx, dy)
        for edge in self.model.edges:
            if edge.src == self.dragging or edge.dst == self.dragging:
                self._update_edge_coords(edge)

    def _on_release(self, event):
        self.dragging = None

    def _on_delete_key(self, event):
        if not self.selected:
            return
        if self.selected[0] == 'node':
            self.model.remove_node(self.selected[1])
        elif self.selected[0] == 'edge':
            self.model.remove_edge(self.selected[1])
        self.selected = None
        self._redraw()

    def _on_escape(self, event):
        self.edge_src = None
        self.selected = None
        self.mode_var.set('select')
        self._mode_changed()

    # ── Analysis ──

    def _log(self, text):
        self.root.after(0, lambda: (
            self.result_text.insert(tk.END, text),
            self.result_text.see(tk.END),
        ))

    def _run_analysis(self):
        if not self.model.nodes:
            messagebox.showwarning("Warning", "No nodes defined")
            return

        sources_a = [n for n in self.model.nodes.values() if n.role == 'source_a']
        sources_b = [n for n in self.model.nodes.values() if n.role == 'source_b']
        if not sources_a or not sources_b:
            messagebox.showwarning(
                "Warning", "Please set both Source A and Source B nodes",
            )
            return

        fail_node_count = sum(1 for n in self.model.nodes.values() if n.failure_target)
        fail_edge_count = sum(1 for e in self.model.edges if e.failure_target)
        total_components = fail_node_count + fail_edge_count
        if total_components == 0:
            messagebox.showwarning(
                "Warning",
                "No failure targets selected.\n"
                "Mark at least one node or edge as a failure target.",
            )
            return
        if total_components > 28:
            messagebox.showwarning(
                "Warning",
                f"Too many failure targets "
                f"({fail_node_count} nodes + {fail_edge_count} edges "
                f"= {total_components}). Maximum is 28.",
            )
            return

        mand_node_count = sum(1 for n in self.model.nodes.values() if n.mandatory)
        mand_edge_count = sum(1 for e in self.model.edges if e.mandatory)

        gcc = shutil.which('gcc')
        if not gcc:
            messagebox.showerror(
                "Error", "gcc not found.\nPlease add gcc to your PATH.",
            )
            return

        outdir = filedialog.askdirectory(title="Select Output Folder")
        if not outdir:
            return

        self.result_text.delete('1.0', tk.END)
        self.result_text.insert(tk.END, (
            f"Starting analysis...\n"
            f"  Failure targets : {fail_node_count} nodes + "
            f"{fail_edge_count} edges = {total_components} components\n"
            f"  Mandatory       : {mand_node_count} nodes + "
            f"{mand_edge_count} edges\n"
            f"  Patterns        : 2^{total_components} = "
            f"{2 ** total_components:,}\n"
            f"Generating C code and compiling...\n"
        ))
        self.result_text.update()

        threading.Thread(
            target=self._analysis_worker,
            args=(gcc, outdir),
            daemon=True,
        ).start()

    def _analysis_worker(self, gcc, outdir):
        try:
            generator = CCodeGenerator()
            code = generator.generate(
                self.model, output_base=os.path.join(outdir, 'result'),
            )
            c_path = os.path.join(outdir, 'analyzer.c')
            with open(c_path, 'w', encoding='utf-8') as f:
                f.write(code)
            self._log(f"C code written: {c_path}\n")

            exe_name = 'analyzer.exe' if sys.platform == 'win32' else 'analyzer'
            exe_path = os.path.join(outdir, exe_name)
            result = subprocess.run(
                [gcc, '-O2', '-o', exe_path, c_path],
                capture_output=True, text=True,
            )
            if result.returncode != 0:
                self._log(f"Compile error:\n{result.stderr}\n")
                return

            self._log("Compile succeeded. Running...\n")
            proc = subprocess.Popen(
                [exe_path], stdout=subprocess.PIPE,
                stderr=subprocess.PIPE, text=True, cwd=outdir,
            )
            for line in proc.stdout:
                self._log(line)
            proc.wait()

            if proc.returncode != 0:
                self._log(f"Runtime error:\n{proc.stderr.read()}\n")
                return

            self._log("\nAnalysis complete.\n")
            csv_files = sorted(
                f for f in os.listdir(outdir)
                if f.startswith('result_') and f.endswith('.csv')
            )
            if csv_files:
                self._log(f"Output files ({len(csv_files)}):\n")
                for fname in csv_files:
                    size = os.path.getsize(os.path.join(outdir, fname))
                    self._log(f"  {fname} ({size / 1024 / 1024:.1f} MB)\n")

            self._generate_graph(outdir)
            self._analyze_reliability(outdir)

        except Exception as ex:
            self._log(f"Error: {ex}\n")

    def _generate_graph(self, outdir):
        summary_path = os.path.join(outdir, 'result_summary.csv')
        if not os.path.exists(summary_path):
            self._log("Summary CSV not found; skipping graph.\n")
            return

        failure_counts = []
        arrival_rates = []
        try:
            with open(summary_path, newline='', encoding='utf-8') as f:
                for row in csv.DictReader(f):
                    failure_counts.append(int(row['failure_count']))
                    arrival_rates.append(float(row['arrival_rate']))
        except Exception as ex:
            self._log(f"Failed to read summary CSV: {ex}\n")
            return

        try:
            import matplotlib
            matplotlib.use('Agg')
            import matplotlib.pyplot as plt
            import matplotlib.ticker as mticker

            rates_pct = [r * 100 for r in arrival_rates]

            fig, ax = plt.subplots(figsize=(10, 5))
            ax.plot(
                failure_counts, rates_pct,
                'b-o', markersize=5, linewidth=2, label='Arrival Rate',
            )
            ax.fill_between(failure_counts, rates_pct, alpha=0.15, color='blue')
            ax.set_xlabel('Number of Failures', fontsize=12)
            ax.set_ylabel('Arrival Rate (%)', fontsize=12)
            ax.set_title('Message Arrival Rate vs Failure Count', fontsize=14)
            ax.set_ylim(0, 105)
            ax.yaxis.set_major_formatter(mticker.FormatStrFormatter('%.0f%%'))
            ax.grid(True, alpha=0.4)
            ax.legend()
            plt.tight_layout()

            png_path = os.path.join(outdir, 'result_graph.png')
            plt.savefig(png_path, dpi=150, bbox_inches='tight')
            plt.close()
            self._log(f"Graph PNG : {png_path}\n")

        except ImportError:
            self._log(
                "matplotlib not installed; PNG graph skipped.\n"
                "  Install with: pip install matplotlib\n"
            )
        except Exception as ex:
            self._log(f"Graph PNG error: {ex}\n")

    # ── Reliability analysis ──

    def _run_reliability(self):
        outdir = filedialog.askdirectory(title="Select Output Folder")
        if not outdir:
            return
        self.result_text.delete('1.0', tk.END)
        threading.Thread(
            target=self._analyze_reliability, args=(outdir,), daemon=True,
        ).start()

    def _analyze_reliability(self, outdir):
        detail_csvs = sorted(
            (
                f for f in os.listdir(outdir)
                if f.startswith('result_') and f.endswith('.csv')
                and 'summary' not in f and 'reliability' not in f
            ),
            key=lambda name: int(name[len('result_'):-len('.csv')]),
        )
        if not detail_csvs:
            self._log("result_*.csv not found. Please run the analysis first.\n")
            return

        first_path = os.path.join(outdir, detail_csvs[0])
        with open(first_path, newline='', encoding='utf-8') as f:
            columns = csv.DictReader(f).fieldnames or []
        component_cols = [c for c in columns if c != 'failure_count']
        if not component_cols:
            self._log("No component columns found.\n")
            return

        half = 1 << (len(component_cols) - 1)
        unreachable_when_failed = {c: 0 for c in component_cols}
        unreachable_when_working = {c: 0 for c in component_cols}
        spof_set = set()

        self._log("Calculating SPOF and Birnbaum importance...\n")
        for fname in detail_csvs:
            with open(os.path.join(outdir, fname), newline='', encoding='utf-8') as f:
                for row in csv.DictReader(f):
                    failure_count = int(row['failure_count'])
                    for col in component_cols:
                        if row[col] == 'F':
                            unreachable_when_failed[col] += 1
                            if failure_count == 1:
                                spof_set.add(col)
                        else:
                            unreachable_when_working[col] += 1

        birnbaum = {
            c: (unreachable_when_failed[c] - unreachable_when_working[c]) / half
            for c in component_cols
        }
        ranked = sorted(birnbaum.items(), key=lambda x: x[1], reverse=True)

        self._log_reliability_report(ranked, spof_set, component_cols)
        self._save_reliability_csv(outdir, ranked, spof_set,
                                   unreachable_when_failed, unreachable_when_working)
        self._generate_reliability_graph(outdir, ranked, spof_set)

    def _log_reliability_report(self, ranked, spof_set, component_cols):
        self._log("\n" + "=" * 52 + "\n")
        self._log("=== Single Points of Failure (SPOF) ===\n")
        spof_list = [c for c in component_cols if c in spof_set]
        if spof_list:
            for component in spof_list:
                self._log(f"  [SPOF] {component}\n")
        else:
            self._log("  No SPOF found\n")

        self._log("\n=== Birnbaum Importance (descending) ===\n")
        self._log(f"  {'Component':<30} {'Importance':>10}  Note\n")
        self._log(f"  {'-' * 50}\n")
        for component, importance in ranked:
            note = "  *SPOF" if component in spof_set else ""
            self._log(f"  {component:<30} {importance:>10.6f}{note}\n")
        self._log("=" * 52 + "\n")

    def _save_reliability_csv(self, outdir, ranked, spof_set,
                              unreachable_when_failed, unreachable_when_working):
        out_path = os.path.join(outdir, 'result_reliability.csv')
        with open(out_path, 'w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            writer.writerow([
                'component', 'is_spof',
                'unreachable_when_failed', 'unreachable_when_working',
                'birnbaum_importance',
            ])
            for component, importance in ranked:
                writer.writerow([
                    component,
                    'Y' if component in spof_set else 'N',
                    unreachable_when_failed[component],
                    unreachable_when_working[component],
                    f'{importance:.8f}',
                ])
        self._log(f"Reliability analysis result saved: {out_path}\n")

    def _generate_reliability_graph(self, outdir, ranked, spof_set):
        try:
            import matplotlib
            matplotlib.use('Agg')
            import matplotlib.pyplot as plt
            import matplotlib.patches as mpatches

            names = [c for c, _ in ranked]
            values = [imp for _, imp in ranked]
            colors = [
                '#EF4444' if c in spof_set else '#3B82F6' for c in names
            ]

            fig_height = max(4, len(names) * 0.38)
            fig, (ax_bar, ax_info) = plt.subplots(
                1, 2, figsize=(14, fig_height),
                gridspec_kw={'width_ratios': [3, 1]},
            )

            bars = ax_bar.barh(
                names, values, color=colors, edgecolor='white', height=0.7,
            )
            ax_bar.invert_yaxis()
            ax_bar.axvline(0, color='#475569', linewidth=0.8, linestyle='--')
            ax_bar.set_xlabel('Birnbaum Importance', fontsize=11)
            ax_bar.set_title(
                'Birnbaum Importance per Component', fontsize=13, pad=10,
            )
            ax_bar.grid(True, axis='x', alpha=0.3)

            val_max = max(values) if values else 1
            val_min = min(values) if values else 0
            ax_bar.set_xlim(min(0, val_min) - 0.05, val_max + 0.15)

            font_size = max(6, min(9, int(180 / max(len(names), 1))))
            for bar, val, name in zip(bars, values, names):
                ax_bar.text(
                    val + val_max * 0.01,
                    bar.get_y() + bar.get_height() / 2,
                    f'{val:.4f}', va='center', ha='left', fontsize=font_size,
                )
                if name in spof_set:
                    ax_bar.text(
                        min(0, val_min) - 0.03,
                        bar.get_y() + bar.get_height() / 2,
                        '*', va='center', ha='center',
                        color='#EF4444', fontsize=font_size + 1,
                    )

            spof_patch = mpatches.Patch(color='#EF4444', label='SPOF')
            norm_patch = mpatches.Patch(color='#3B82F6', label='Normal')
            ax_bar.legend(
                handles=[spof_patch, norm_patch], loc='lower right', fontsize=9,
            )

            ax_info.axis('off')
            spof_list = [c for c in names if c in spof_set]
            info_lines = [
                f"SPOF  ({len(spof_list)} / {len(names)} components)",
                '-' * 28,
            ]
            if spof_list:
                info_lines += [f'  * {c}' for c in spof_list]
            else:
                info_lines.append('  (none)')

            ax_info.text(
                0.05, 0.97, '\n'.join(info_lines),
                transform=ax_info.transAxes, va='top', ha='left',
                fontsize=9, fontfamily='monospace',
                bbox=dict(
                    boxstyle='round,pad=0.6',
                    facecolor='#FEF2F2' if spof_list else '#F0FDF4',
                    edgecolor='#EF4444' if spof_list else '#22C55E',
                    linewidth=1.5,
                ),
            )

            plt.suptitle('Reliability Analysis', fontsize=14, y=1.01)
            plt.tight_layout()

            png_path = os.path.join(outdir, 'result_reliability_graph.png')
            plt.savefig(png_path, dpi=150, bbox_inches='tight')
            plt.close()
            self._log(f"Reliability graph saved: {png_path}\n")

        except ImportError:
            self._log(
                "matplotlib is not installed; skipping graph.\n"
                "  Install it with: pip install matplotlib\n"
            )
        except Exception as ex:
            self._log(f"Reliability graph generation error: {ex}\n")

    # ── File operations ──

    def _export_c(self):
        if not self.model.nodes:
            messagebox.showwarning("Warning", "No nodes defined")
            return
        path = filedialog.asksaveasfilename(
            defaultextension='.c', filetypes=[('C source', '*.c')],
        )
        if not path:
            return
        code = CCodeGenerator().generate(self.model)
        with open(path, 'w', encoding='utf-8') as f:
            f.write(code)
        messagebox.showinfo("Done", f"C code exported:\n{path}")

    def _save(self):
        path = filedialog.asksaveasfilename(
            defaultextension='.json', filetypes=[('JSON', '*.json')],
        )
        if not path:
            return
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(self.model.to_dict(), f, ensure_ascii=False, indent=2)

    def _load(self):
        path = filedialog.askopenfilename(filetypes=[('JSON', '*.json')])
        if not path:
            return
        with open(path, 'r', encoding='utf-8') as f:
            self.model.from_dict(json.load(f))
        self.selected = None
        self._redraw()

    def _load_preset(self):
        if self.model.nodes:
            if not messagebox.askyesno(
                "Confirm", "Discard current topology and load preset?",
            ):
                return
        self.model.from_dict(make_preset_24())
        self.selected = None
        self._redraw()
        self.status_var.set("Loaded preset (24-node with cross paths)")

    def _clear(self):
        if self.model.nodes:
            if not messagebox.askyesno("Confirm", "Clear all nodes and edges?"):
                return
        self.model.clear()
        self.selected = None
        self._redraw()


if __name__ == '__main__':
    root = tk.Tk()
    app = App(root)

    def _shutdown(sig, frame):
        root.destroy()
        sys.exit(0)

    signal.signal(signal.SIGINT, _shutdown)
    signal.signal(signal.SIGTERM, _shutdown)
    if hasattr(signal, 'SIGTSTP'):
        signal.signal(signal.SIGTSTP, _shutdown)

    root.mainloop()
