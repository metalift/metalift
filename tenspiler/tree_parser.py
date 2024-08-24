import argparse
import glob
import os
from typing import Any, Optional

from tree_sitter import Node
from tree_sitter_languages import get_language, get_parser


def find_cc_file_paths(file_path: str) -> list[str]:
    all_cc_file_paths: list[str] = []
    if os.path.isdir(file_path):
        # Use glob to recursively find all *.cc files in the directory
        cc_files = glob.glob(os.path.join(file_path, "**", "*.cc"), recursive=True)
        for file in cc_files:
            all_cc_file_paths.append(file)
    else:
        # Check if the file is a .cc file
        if file_path.endswith(".cc"):
            all_cc_file_paths.append(file_path)
    return all_cc_file_paths


class ParserError(Exception):
    pass


LANGUAGE = get_language("cpp")
PARSER = get_parser("cpp")

example1 = """
vector<int> normal_blend_f(vector<int> base, vector<int> active, int opacity)
{
  vector<int> out;
  for (int i = 0; i < base.size(); ++i)
    out.push_back(opacity * active[i] + (1 - opacity) * base[i]);
  return out;
}
"""

example2 = """
vector<int> normal_blend_8(vector<int> base, vector<int> active, int opacity)
{
  vector<int> out;
  for (int i = 0; i < base.size(); ++i)
    out.push_back(opacity * active[i] + (32 - opacity) * base[i]);

  return out;
}
"""

example3 = """
int mag_array(vector<int> a, int n) {
    int i;
    int sum = 0;
    for(i = 0; i < n; ++i){
        sum += a[i] * a[i];
    }
    return sum;
}
"""

example4 = """
vector<vector<int>> matrix_add_matrix(vector<vector<int>> from_matrix, vector<vector<int>> to_matrix)
{
    int i, j;
    vector<vector<int>> out;
    for (i = 0; i < from_matrix.size(); ++i) {
        vector<int> row_vec;
        for (j = 0; j < from_matrix[0].size(); ++j) {
            row_vec.push_back(from_matrix[i][j] + to_matrix[i][j]);
        }
        out.push_back(row_vec);
    }
    return out;
}
"""
example5 = """
vector<int> lmsfir2(int NTAPS, vector<int> input, vector<int> coefficient, int error) {
    vector<int> out;
    for (int i = 0; i < NTAPS - 1; ++i) {
        int curr = coefficient[i] + input[i] * error;
        out.push_back(curr);
    }
    return out;
}

"""


example6 = """
vector<vector<int>> screen_blend_8(vector<vector<int>> base, vector<vector<int>> active)
{
    vector<vector<int>> out;
    int m = base.size();
    int n = base[0].size();
    for (int row = 0; row < m; row++) {
        vector<int> row_vec;
        for (int col = 0; col < n; col++) {
            int pixel = base[row][col] + active[row][col] - (base[row][col] * active[row][col]) / 32;
            row_vec.push_back(pixel);
        }
        out.push_back(row_vec);
    }
    return out;
}
"""


example7 = """
vector<vector<int>> linear_burn_8(vector<vector<int>> base, vector<vector<int>> active)
{
    vector<vector<int>> out;
    int m = base.size();
    int n = base[0].size();
	for (int row = 0; row < m; row++) {
        vector<int> row_vec;
		for (int col = 0; col < n; col++) {
            int pixel = (base[row][col] + active[row][col]) - 32;
			row_vec.push_back(pixel);
		}
		out.push_back(row_vec);
	}
	return out;
}
"""

example8 = """
vector<vector<int>> lighten_blend_8(vector<vector<int>> base, vector<vector<int>> active)
{
    vector<vector<int>> out;
    int m = base.size();
    int n = base[0].size();
	for (int row = 0; row < m; row++) {
        vector<int> row_vec;
		for (int col = 0; col < n; col++) {
			int pixel;
			if (base[row][col] < active[row][col])
				pixel = active[row][col];
			else
				pixel = base[row][col];
			row_vec.push_back(pixel);
		}
		out.push_back(row_vec);
	}
	return out;
}
"""

example9 = """
int softmax_part1(vector<int> input, int max_pos) {
    int max_val = input[0];
    for (int i = 1; i < max_pos; i++)
        if (input[i] > max_val)
            max_val = input[i];
    return max_val;
}
"""


#####pattern matching queries
# matches the for loop
loop_query = "(for_statement)@stmt_str"
double_loop_query = """'
(for_statement body: (compound_statement (for_statement)))
"""

# Matches the body of a single for loop that has a push_back expression
outer_loop_push_query = """
(for_statement body: (compound_statement (expression_statement (call_expression)@call_expr)@expr_stmt))
"""
inner_loop_push_query = """
(for_statement body: (compound_statement (for_statement body: (compound_statement (expression_statement (call_expression)@call_expr)@expr_stmt))))
"""

# Matches the body of the for loop that has a compound statement
# An example of a compound statment is sum += a[i] * a[i];
outer_loop_compound_query = """
(function_definition body: (compound_statement (for_statement body: (compound_statement (expression_statement)@expr))))
"""
inner_loop_compound_query = """
(for_statement
  body: (compound_statement (for_statement (compound_statement (expression_statement)@expr)))
)
"""

### declation and compound statement
# This is for declaring variables without initialization, such as int i;
decl_query = """
(declaration declarator: (identifier)@id)
"""
init_decl_query = """
(declaration (init_declarator (identifier))@id)
"""

### if statement in a compound statement
if_query = """
(if_statement)@if_stmt
"""


def _capture_to_text(capture: tuple[Node, str]) -> str:
    return capture[0].text.decode()


def _node_to_text(node: Node) -> str:
    return node.text.decode()


def build_expression_tree(node):
    if node.type == "binary_expression" or node.type == "assignment_expression":
        left_child = build_expression_tree(node.child_by_field_name("left"))
        operator = node.child_by_field_name("operator").text.decode()
        right_child = build_expression_tree(node.child_by_field_name("right"))
        return {
            "type": "operator",
            "operator": operator,
            "left": left_child,
            "right": right_child,
        }
    elif node.type == "identifier":
        return {"type": "identifier", "value": node.text.decode()}
    elif node.type == "subscript_expression":
        array_name = build_expression_tree(node.child_by_field_name("argument"))
        index = build_expression_tree(node.child_by_field_name("indices"))
        return {"type": "array_access", "array": array_name, "index": index}
    elif node.type == "parenthesized_expression":
        # Unwrap the parenthesized expression
        return build_expression_tree(node.children[1])
    elif node.type == "number_literal":
        return {"type": "literal", "value": node.text.decode()}
    elif node.type == "expression_statement":
        return build_expression_tree(node.children[0])
    elif node.type == "declaration":
        return build_expression_tree(node.child_by_field_name("declarator"))
    elif node.type == "identifier":
        return {"type": "identifier", "value": node.text.decode()}
    elif node.type == "init_declarator":
        return build_expression_tree(node.child_by_field_name("value"))
    elif node.type == "if_statement":
        return {
            "type": "if_statement",
            "condition": build_expression_tree(node.children[1]),
            "then": build_expression_tree(node.children[2]),
            "else": build_expression_tree(node.children[3]),
        }
    else:
        return {"type": node.type, "value": node.text.decode()}


def preorder_traversal(node):
    if node["type"] == "operator":
        # Get the operator
        operator = node["operator"]
        # Traverse left child
        left_expr = preorder_traversal(node["left"])
        # Traverse right child
        right_expr = preorder_traversal(node["right"])
        # Combine into an expression
        return f"({operator} {left_expr} {right_expr})"
    elif node["type"] == "identifier":
        return node["value"]
    elif node["type"] == "literal":
        return node["value"]
    elif node["type"] == "array_access":
        array_name = preorder_traversal(node["array"])
        index = preorder_traversal(node["index"])
        return f"{array_name}[{index}]"
    elif node["type"] == "if_statement":
        condition = preorder_traversal(node["condition"])
        then_stmt = preorder_traversal(node["then"])
        else_stmt = preorder_traversal(node["else"])
        return f"if ({condition}) then {{ {then_stmt} }} else {{ {else_stmt} }}"
    else:
        return node["value"]


def find_init_decl_to_var(var_name: str, tree_node: Node):
    init_decl_stmts = LANGUAGE.query(init_decl_query).captures(tree_node)
    for init_decl_stmt in init_decl_stmts:
        decl_node = init_decl_stmt[0]
        if decl_node.child_by_field_name("declarator").text.decode() == var_name:
            return decl_node
    return None


def find_compute(tree_node: Node) -> dict[str, Any]:
    # Get number of loops
    loops = LANGUAGE.query(loop_query).captures(tree_node)
    num_loops = len(loops)
    if num_loops not in {1, 2}:
        raise ParserError(
            f"Only singly or doubly nested loops are supported, but found {num_loops} loops"
        )

    # Check if loop has if statement. For now we assume the if statement is always inside the
    # innermost loop
    if_stmts = LANGUAGE.query(if_query).captures(tree_node)
    num_if_stmts = len(if_stmts)
    if num_if_stmts not in {0, 1}:
        raise ParserError(
            f"Only zero or one if statements are supported, but found {num_if_stmts} if statements"
        )

    if len(if_stmts) > 0:
        if_stmt_node = if_stmts[0][0]
        if_condition = if_stmt_node.child_by_field_name("condition")
        if_then_stmt = if_stmt_node.child_by_field_name("consequence")
        if_else_stmt = if_stmt_node.child_by_field_name("alternative")

        print(f"If condition: {_node_to_text(if_condition)}")
        print(f"If then statement: {_node_to_text(if_then_stmt)}")
        if if_else_stmt != None:
            print(f"If else statement: {_node_to_text(if_else_stmt)}")
            tree = build_expression_tree(if_stmt_node)
            return tree
        else:
            tree = build_expression_tree(if_then_stmt)
            return tree

    # Check if tree node loop body has push statements (e.g. out.push_back(curr);)
    is_single_loop = num_loops == 1
    if is_single_loop:
        push_stmts = LANGUAGE.query(outer_loop_push_query).captures(tree_node)
    else:
        push_stmts = LANGUAGE.query(inner_loop_push_query).captures(tree_node)
    push_stmts = [push_stmt for push_stmt in push_stmts if push_stmt[1] == "call_expr"]
    num_push_stmts = len(push_stmts)
    if num_push_stmts not in {0, 1}:
        raise ParserError(
            f"Expected <= 1 push statements in the innermost loop, but found {len(push_stmts)}"
        )
    if num_push_stmts > 0:
        for push_stmt in push_stmts:
            print(f"Push statement: {_capture_to_text(push_stmt)}")
            push_arg = push_stmt[0].child_by_field_name("arguments").children[1]
            if push_arg.type == "identifier":
                decl_node = find_init_decl_to_var(push_arg.text.decode(), tree_node)
                tree = build_expression_tree(decl_node)
                return tree
            else:
                tree = build_expression_tree(push_arg)
                return tree

    # Check if tree node loop body has compound statements (e.g. sum += a[i] * a[i];)
    inner_loop_compound_stmts = LANGUAGE.query(inner_loop_compound_query).captures(
        tree_node
    )
    outer_loop_compound_stmts = LANGUAGE.query(outer_loop_compound_query).captures(
        tree_node
    )
    assert len(inner_loop_compound_stmts) <= 1
    assert len(outer_loop_compound_stmts) <= 1

    if not is_single_loop:
        # TODO(jie): need to filter out push back statements here
        inner_tree: Optional[Node] = None
        outer_tree: Optional[Node] = None

        if len(inner_loop_compound_stmts) > 0:
            inner_most_compound = inner_loop_compound_stmts[0]
            print(
                f"Innermost compound statement: {_capture_to_text(inner_most_compound)}"
            )
            inner_tree = build_expression_tree(inner_most_compound[0])
        if len(outer_loop_compound_stmts) > 0:
            outer_loop_push_stmts = LANGUAGE.query(outer_loop_push_query).captures(
                tree_node
            )
            outer_loop_push_stmts = [
                stmt for stmt in outer_loop_push_stmts if stmt[1] == "expr_stmt"
            ]
            outer_loop_push_nodes = [stmt[0] for stmt in outer_loop_push_stmts]
            outer_loop_compound_capture = outer_loop_compound_stmts[0]
            outer_loop_compound_node = outer_loop_compound_capture[0]
            if outer_loop_compound_node not in outer_loop_push_nodes:
                outer_most_compound = outer_loop_compound_stmts[0]
                print(
                    f"Outermost compound statement: {_capture_to_text(outer_loop_compound_capture)}"
                )
                outer_tree = build_expression_tree(outer_most_compound[0])
        if inner_tree is None:
            return outer_tree
        elif outer_tree is None:
            return inner_tree
        elif inner_tree is not None and outer_tree is not None:
            return inner_tree, outer_tree
        else:
            return None
    else:
        if len(outer_loop_compound_stmts) > 0:
            outer_most_compound = outer_loop_compound_stmts[0]
            print(
                f"Outermost compound statement: {_capture_to_text(outer_most_compound)}"
            )
            tree = build_expression_tree(outer_most_compound[0])
            return tree


if __name__ == "__main__":
    # Set up some global variables / paths

    # reading arguments from the command line
    parser = argparse.ArgumentParser()
    parser.add_argument("--file-path", type=str, required=True)
    args = parser.parse_args()

    cc_file_paths = find_cc_file_paths(args.file_path)

    for idx, cc_file_path in enumerate(cc_file_paths):
        # benchmark_name = cc_file_path.split("/")[-1].split(".")[0]
        # if benchmark_name in {"transformer_part1", "transformer_part2"}:
        #     continue
        print(f"Reading file {idx} of {len(cc_file_paths)}: ", cc_file_path)
        with open(cc_file_path) as f:
            source_code = f.read()
        print(f"Source code: {source_code}")
        tree = PARSER.parse(source_code.encode())
        root_node = tree.root_node
        parsed_tree = find_compute(root_node)
        print("Preorder traversal: ")
        if isinstance(parsed_tree, tuple):
            for tree in parsed_tree:
                print(preorder_traversal(tree))
        else:
            print(preorder_traversal(parsed_tree))
            # print(preorder_traversal(parsed_tree))
            # if parsed_tree == None:
            #     import pdb

            # pdb.set_trace()
