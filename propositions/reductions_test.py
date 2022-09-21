# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/reductions_test.py

"""Tests for the propositions.reductions module."""

from propositions.syntax import *
from propositions.semantics import *
from propositions.reductions import *

TEST_GRAPHS = [
    ((1, frozenset()), True), # empty graph
    ((3, frozenset()), True), # empty graph
    ((2, frozenset({(1,2)})), True), # single edge
    ((3, frozenset({(1,2) ,(1,3), (2,3)})), True), # 3-clique
    ((4, frozenset({(1,2), (1,3), (2,3), (1,4), (2,4), (3,4)})),
     False), # 4-clique
    ((4, frozenset({(1,2), (1,3), (2,3), (1,4), (2,4)})),
     True), # 4-clique - edge
    ((5, frozenset({(2,3), (2,4), (3,4), (2,5), (3,5), (4,5), (1,2), (1,4)})),
     False), # 4-clique + edges  
    ((5, frozenset({(1,2), (2,3), (3,4), (4,5), (5,1)})), True)] # 5-cycle
    #((6, frozenset({(1,2), (2,3), (3,4), (4,5), (5,1), (1,6), (2,6), (3,6),
    #                (4,6), (5,6)})), False)]# 5-cycle + vertex

def test_graph3coloring_to_formula(debug=False):
    for (graph, satisfiable) in TEST_GRAPHS:
        if debug:
            print("Testing graph3coloring_to_formula on", graph)
        formula = graph3coloring_to_formula(graph)
        assert is_satisfiable(formula) == satisfiable

def test_assignment_to_3coloring(debug=False):
    for (graph, satisfiable) in TEST_GRAPHS:
        if not satisfiable:
            continue      
        if debug:
            print("Testing assignment_to_3coloring on graph", graph)
        formula = graph3coloring_to_formula(graph)
        for assignment in all_models(list(formula.variables())):
            if evaluate(formula, assignment):
                coloring = assignment_to_3coloring(graph, assignment)
                assert is_valid_3coloring(graph, coloring)

def test_tricolor_graph(debug=False):
    for (graph, satisfiable) in TEST_GRAPHS:
        if not satisfiable:
            if debug:
                print("Verifying that Graph", graph, "cannot be 3-colored")
            assert tricolor_graph(graph) is None
        else:
            coloring = tricolor_graph(graph)
            if debug:
                print("Graph", graph, "can be 3-colored as", coloring)
            assert is_valid_3coloring(graph, coloring)

def test_ex2_opt(debug=False):
    test_graph3coloring_to_formula(debug)
    test_assignment_to_3coloring(debug)
    test_tricolor_graph(debug)

def test_all(debug=False):
    test_ex2_opt(debug)
