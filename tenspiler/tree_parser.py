import argparse
import glob
import os
from typing import Any, Optional, Union

from tree_sitter import Node
from tree_sitter_languages import get_language, get_parser

from metalift.frontend.llvm import Driver
from metalift.ir import Bool, Int, List, Matrix, ObjectT, choose
from metalift.vc_util import and_objects


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

template_types_query = """
(function_declarator (parameter_list (parameter_declaration(template_type))@type))
"""

primitive_types_query = """
(function_declarator (parameter_list (parameter_declaration(primitive_type))@type))
"""


def _capture_to_text(capture: tuple[Node, str]) -> str:
    return capture[0].text.decode()


def _node_to_text(node: Node) -> str:
    return node.text.decode()


def build_type_expression_tree(
    node: Node, target_type: str, all_vars_by_name: dict[str, ObjectT]
) -> Union[dict[str, Any], str]:
    def helper(node: Node):
        if node.type == "binary_expression" or node.type == "assignment_expression":
            left_child = helper(node.child_by_field_name("left"))
            if isinstance(left_child, dict):
                left_type = left_child["return_type"]
            else:
                left_type = left_child
            right_child = helper(node.child_by_field_name("right"))
            if isinstance(right_child, dict):
                right_type = right_child["return_type"]
            else:
                right_type = right_child
            operator = node.child_by_field_name("operator").text.decode()
            return_type = "scalar"
            if (left_type, right_type) in {
                ("vector", "int"),
                ("int", "vector"),
                ("vector", "vector"),
            }:
                return_type = "vector"
            elif (left_type, right_type) in {
                ("matrix", "matrix"),
                ("matrix", "int"),
                ("int", "matrix"),
            }:
                return_type = "matrix"
            return {
                "type": "operator",
                "operator": operator,
                "left": left_child,
                "right": right_child,
                "return_type": return_type,
            }
        elif node.type == "identifier":
            var_name = node.text.decode()
            var_type = get_str_type(all_vars_by_name[var_name])
            if var_type == "scalar":
                return "scalar"
            else:
                return target_type
        elif node.type == "subscript_expression":
            return target_type
        elif node.type == "parenthesized_expression":
            # Unwrap the parenthesized expression
            return helper(node.children[1])
        elif node.type == "number_literal":
            return "scalar"
        elif node.type == "expression_statement":
            return helper(node.children[0])
        elif node.type == "declaration":
            return helper(node.child_by_field_name("declarator"))
        elif node.type == "init_declarator":
            return helper(node.child_by_field_name("value"))
        elif node.type == "if_statement":
            return {
                "type": "if_statement",
                "condition": helper(node.children[1]),
                "then": helper(node.children[2]),
                "else": helper(node.children[3]),
            }
        else:
            return {"type": node.type, "value": node.text.decode()}

    return helper(node)


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


def preorder_traversal_with_objs(
    type_expr_tree: Union[dict[str, Any], str],
    vars_by_type_str: dict[str, list[ObjectT]],
):
    if isinstance(type_expr_tree, str):
        return choose(*vars_by_type_str[type_expr_tree])
    if isinstance(type_expr_tree, dict):
        if type_expr_tree["type"] == "operator":
            operator = type_expr_tree["operator"]
            left_expr = preorder_traversal_with_objs(
                type_expr_tree["left"], vars_by_type_str
            )
            right_expr = preorder_traversal_with_objs(
                type_expr_tree["right"], vars_by_type_str
            )
            # TODO(jie): support matrix
            if operator == "+":
                return List.add(left_expr, right_expr)
            elif operator == "-":
                return List.sub(left_expr, right_expr)
            elif operator == "*":
                return List.mul(left_expr, right_expr)
            elif operator == "/":
                return List.div(left_expr, right_expr)
            else:
                raise ParserError(f"Unsupported operator: {operator}")
        else:
            raise ParserError(f"Unsupported type: {type_expr_tree['type']}")


def find_init_decl_to_var(var_name: str, tree_node: Node):
    init_decl_stmts = LANGUAGE.query(init_decl_query).captures(tree_node)
    for init_decl_stmt in init_decl_stmts:
        decl_node = init_decl_stmt[0]
        if decl_node.child_by_field_name("declarator").text.decode() == var_name:
            return decl_node
    return None


def find_input_type(var_name: str, tree_node: Node) -> str:
    template_input_types = LANGUAGE.query(template_types_query).captures(tree_node)
    primitive_input_types = LANGUAGE.query(primitive_types_query).captures(tree_node)
    for input_type in template_input_types + primitive_input_types:
        curr_var_type, curr_var_name = input_type[0].text.decode().split(" ")
        if curr_var_name == var_name:
            if curr_var_type == "vector<int>":
                return "vector"
            elif curr_var_type == "vector<vector<int>>":
                return "matrix"
            else:
                raise ParserError(f"Unsupported input type: {curr_var_type}")
    return None


def make_input_variables(tree_node: Node, driver: Driver) -> dict[str, ObjectT]:
    template_input_types = LANGUAGE.query(template_types_query).captures(tree_node)
    primitive_input_types = LANGUAGE.query(primitive_types_query).captures(tree_node)
    input_vars: dict[str, ObjectT] = {}
    for input_type in template_input_types + primitive_input_types:
        curr_var_type, curr_var_name = input_type[0].text.decode().split(" ")
        if curr_var_type == "vector<int>":
            input_vars[curr_var_name] = List(Int, curr_var_name)
        elif curr_var_type == "vector<vector<int>>":
            input_vars[curr_var_name] = Matrix(Int, curr_var_name)
        elif curr_var_type == "int":
            input_vars[curr_var_name] = Int(curr_var_name)
        else:
            raise ParserError(f"Unsupported input type: {curr_var_type}")
    driver.add_var_objects(list(input_vars.values()))
    return input_vars


def find_compute_from_node(
    tree_node: Node,
) -> Union[dict[str, Any], tuple[dict[str, Any], dict[str, Any]]]:
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
        if_condition_node = if_stmt_node.child_by_field_name("condition")
        if_then_stmt_node = if_stmt_node.child_by_field_name("consequence")
        if_else_stmt_node = if_stmt_node.child_by_field_name("alternative")

        print(f"If condition: {_node_to_text(if_condition_node)}")
        print(f"If then statement: {_node_to_text(if_then_stmt_node)}")
        if if_else_stmt_node is not None:
            print(f"If else statement: {_node_to_text(if_else_stmt_node)}")
            return if_stmt_node
        else:
            return if_then_stmt_node

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
                return decl_node
            else:
                return push_arg

    # Check if tree node loop body has compound statements (e.g. sum += a[i] * a[i];)
    inner_loop_compound_stmts = LANGUAGE.query(inner_loop_compound_query).captures(
        tree_node
    )
    inner_loop_compound_nodes = [stmt[0] for stmt in inner_loop_compound_stmts]
    outer_loop_compound_stmts = LANGUAGE.query(outer_loop_compound_query).captures(
        tree_node
    )
    outer_loop_compound_nodes = [stmt[0] for stmt in outer_loop_compound_stmts]
    # If we have a double loop, we exclude push_back statements from the outer loop compound statements
    if not is_single_loop:
        outer_loop_push_stmts = LANGUAGE.query(outer_loop_push_query).captures(
            tree_node
        )
        outer_loop_push_stmts = [
            stmt for stmt in outer_loop_push_stmts if stmt[1] == "expr_stmt"
        ]
        outer_loop_push_nodes = [stmt[0] for stmt in outer_loop_push_stmts]
        outer_loop_compound_nodes = [
            stmt
            for stmt in outer_loop_compound_nodes
            if stmt not in outer_loop_push_nodes
        ]
    assert len(inner_loop_compound_nodes) <= 1
    assert len(outer_loop_compound_nodes) <= 1

    if not is_single_loop:
        # TODO(jie): need to filter out push back statements here
        inner_tree: Optional[Node] = None
        outer_tree: Optional[Node] = None

        if len(inner_loop_compound_nodes) > 0:
            inner_most_compound_node = inner_loop_compound_nodes[0]
            print(
                f"Innermost compound statement: {_node_to_text(inner_most_compound_node)}"
            )
        if len(outer_loop_compound_nodes) > 0:
            outer_most_compound_node = outer_loop_compound_nodes[0]
            print(
                f"Outermost compound statement: {_node_to_text(outer_most_compound_node)}"
            )
        if inner_most_compound_node is None and outer_most_compound_node is not None:
            return outer_most_compound_node
        elif inner_most_compound_node is not None and outer_most_compound_node is None:
            return inner_most_compound_node
        elif (
            inner_most_compound_node is not None
            and outer_most_compound_node is not None
        ):
            return inner_most_compound_node, outer_most_compound_node
        else:
            return None
    else:
        if len(outer_loop_compound_stmts) > 0:
            outer_most_compound = outer_loop_compound_stmts[0]
            print(
                f"Outermost compound statement: {_capture_to_text(outer_most_compound)}"
            )
            return outer_most_compound[0]


def find_compute_from_file(
    file_path: str,
) -> Union[dict[str, Any], tuple[dict[str, Any], dict[str, Any]]]:
    return find_compute_from_node(find_root_node_from_file(file_path))


def find_root_node_from_file(file_path: str) -> Node:
    with open(file_path) as f:
        source_code = f.read()
    print(f"Reading file {file_path}: ", file_path)
    print(f"Source code: {source_code}")
    tree = PARSER.parse(source_code.encode())
    return tree.root_node


def is_int_vector(var: ObjectT) -> bool:
    return var.type == List[Int]


def is_int_matrix(var: ObjectT) -> bool:
    return var.type == Matrix[Int] or var.type == List[List[Int]]


def is_int_scalar(var: ObjectT) -> bool:
    return var.type == Int


def get_vector_vars(vars: list[ObjectT]) -> list[ObjectT]:
    return [var for var in vars if is_int_vector(var)]


def get_scalar_vars(vars: list[ObjectT]) -> list[ObjectT]:
    return [var for var in vars if is_int_scalar(var)]


def get_matrix_vars(vars: list[ObjectT]) -> list[ObjectT]:
    return [var for var in vars if is_int_matrix(var)]


def get_str_type(var: ObjectT) -> str:
    if is_int_vector(var):
        return "vector"
    elif is_int_matrix(var):
        return "matrix"
    elif is_int_scalar(var):
        return "scalar"
    else:
        raise ParserError(f"Unsupported type: {var.type}")


def get_outer_loop_bounds(
    loop_bounds: list[tuple[Any]], vars_by_name: dict[str, ObjectT]
) -> list[Bool]:
    outer_loop_bounds = loop_bounds[0]
    op = outer_loop_bounds[-1][1]
    if op == "<":
        left_bound = outer_loop_bounds[0][-1]
        right_bound = outer_loop_bounds[-1][-1]
        if isinstance(left_bound, int):
            left_bound = Int(left_bound)
        else:
            left_bound = vars_by_name[left_bound]
        if isinstance(right_bound, int):
            right_bound = Int(right_bound)
        else:
            right_bound = vars_by_name[right_bound]
        return [left_bound, right_bound]
    else:
        raise ParserError(f"Unsupported operator: {op}")


def get_outer_loop_var(
    loop_bounds: list[tuple[Any]], vars_by_name: dict[str, ObjectT]
) -> Int:
    outer_loop_bounds = loop_bounds[0]
    outer_loop_var_name = outer_loop_bounds[0][0]
    outer_loop_var = vars_by_name[outer_loop_var_name]
    if outer_loop_var.type != Int:
        raise ParserError(
            f"Outer loop variable must be of type int, but got {outer_loop_var.type}"
        )
    return outer_loop_var


def get_vars_by_type_str(vars: list[ObjectT]) -> list[ObjectT]:
    return {
        "vector": get_vector_vars(vars),
        "matrix": get_matrix_vars(vars),
        "scalar": get_scalar_vars(vars),
    }


def get_vars_by_name(vars: list[ObjectT]) -> dict[str, ObjectT]:
    return {var.src.name(): var for var in vars}


def get_outer_loop_inv(
    writes: list[ObjectT],
    reads: list[ObjectT],
    in_scope: list[ObjectT],
    relaxed: bool,
    loop_bounds: list[tuple[Any]],
    compute_node: Node,
) -> Bool:
    writes_by_name = {var.src.name(): var for var in writes}
    reads_by_name = {var.src.name(): var for var in reads}
    in_scope_by_name = {var.src.name(): var for var in in_scope}
    all_vars_by_name = {**writes_by_name, **reads_by_name, **in_scope_by_name}

    # First get the loop bounds
    left_bound, right_bound = get_outer_loop_bounds(loop_bounds, all_vars_by_name)
    loop_var = get_outer_loop_var(loop_bounds, all_vars_by_name)
    loop_conditions = [
        loop_var >= left_bound,
        loop_var <= right_bound,
    ]

    # Then we get the expression tree
    # Find in this loop what needs to be on the lhs of loop invariant
    write_conditions: list[Bool] = []
    loop_var_name = loop_bounds[0][0][0]
    writes_needed = [
        var
        for var in writes
        if var.src.name() != loop_var_name and not var.src.name().endswith(".tmp")
    ]
    for write_var in writes_needed:
        type_expr_tree = build_type_expression_tree(
            compute_node, get_str_type(write_var), all_vars_by_name
        )
        read_and_in_scope_vars_by_type: dict[str, list[ObjectT]] = {}
        scalar_vars = get_scalar_vars(reads + in_scope)
        vector_vars = get_vector_vars(reads + in_scope)
        matrix_vars = get_matrix_vars(reads + in_scope)
        if len(scalar_vars) > 0:
            read_and_in_scope_vars_by_type["scalar"] = scalar_vars
        if len(vector_vars) > 0:
            vector_vars = [choose(*vector_vars)[left_bound:loop_var]]
            read_and_in_scope_vars_by_type["vector"] = vector_vars
        if len(matrix_vars) > 0:
            read_and_in_scope_vars_by_type["matrix"] = matrix_vars
        obj_expr_tree = preorder_traversal_with_objs(
            type_expr_tree, read_and_in_scope_vars_by_type
        )
        write_conditions.append(write_var == obj_expr_tree)
    return and_objects(*loop_conditions, *write_conditions)


def get_ps(
    writes: list[ObjectT],
    reads: list[ObjectT],
    in_scope: list[ObjectT],
    relaxed: bool,
    loop_bounds: list[tuple[Any]],
    compute_node: Node,
) -> Bool:
    if len(writes) != 1:
        raise ParserError("Expected only one write variable in ps")
    rv = writes[0]
    all_vars_by_name = get_vars_by_name(writes + reads + in_scope)
    left_bound, right_bound = get_outer_loop_bounds(loop_bounds, all_vars_by_name)
    read_vars_by_type: dict[str, list[ObjectT]] = {}
    scalar_vars = get_scalar_vars(reads)
    vector_vars = get_vector_vars(reads)
    matrix_vars = get_matrix_vars(reads)
    if len(scalar_vars) > 0:
        read_vars_by_type["scalar"] = scalar_vars
    if len(vector_vars) > 0:
        vector_vars = [choose(*vector_vars)[left_bound:right_bound]]
        read_vars_by_type["vector"] = vector_vars
    if len(matrix_vars) > 0:
        matrix_vars = [choose(*matrix_vars)[left_bound:right_bound]]
        read_vars_by_type["vector"] = matrix_vars
    type_expr_tree = build_type_expression_tree(
        compute_node, get_str_type(rv), all_vars_by_name
    )
    obj_expr_tree = preorder_traversal_with_objs(type_expr_tree, read_vars_by_type)
    return rv == obj_expr_tree


if __name__ == "__main__":
    # reading arguments from the command line
    parser = argparse.ArgumentParser()
    parser.add_argument("--file-path", type=str, required=True)
    args = parser.parse_args()

    cc_file_paths = find_cc_file_paths(args.file_path)

    for idx, cc_file_path in enumerate(cc_file_paths):
        print(f"Processing file {idx} of {len(cc_file_paths)}")
        parsed_tree = find_compute_from_file(cc_file_path)
        print("Preorder traversal: ")
        if isinstance(parsed_tree, tuple):
            for tree in parsed_tree:
                print(preorder_traversal(tree))
        else:
            print(preorder_traversal(parsed_tree))
