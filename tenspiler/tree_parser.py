from tree_sitter import Node
from tree_sitter_languages import get_language, get_parser


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
loop_query = "(for_statement) @stmt_str"

# Matches the body of the for loop that has a push_back expression
body_push_query = """
(for_statement
  body: (expression_statement
          (call_expression)@expr
        )
)
"""

# Matches the body of the for loop that has a compound statement
# An example of a compound statment is sum += a[i] * a[i];
body_compound_query = """
(for_statement
  body: (compound_statement (expression_statement) @comp)
)
"""

### declation and compound statement
body_decl_query = """
(for_statement
  body: (compound_statement (declaration) @comp)
)
"""

### if statement in a compound statement
if_query = """
(if_statement)@if_stmt
"""

# if condition
if_condition_query = """
(if_statement condition: (condition_clause value: (binary_expression) @expr))
"""

# The then clause of the if statement
if_then_query = """
(if_statement
   consequence: (expression_statement)@expr)
"""

# The else clause of the if statement
if_else_query = """
(if_statement
   alternative: (else_clause (expression_statement)@expr))
"""


def _capture_to_text(capture: tuple[Node, str]) -> str:
    return capture[0].text.decode()


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
    elif node.type == "call_expression":
        return build_expression_tree(node.child_by_field_name("arguments"))
    elif node.type == "argument_list":
        return build_expression_tree(node.children[1])
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


def find_compute(tree_node):
    # Get number of loops
    captures = LANGUAGE.query(loop_query).captures(tree_node)
    num_loops = len(captures)
    if num_loops not in {1, 2}:
        raise ParserError(
            f"Only singly or doubly nested loops are supported, but found {num_loops} loops"
        )

    # Check if loop has if statement
    if_stmts = LANGUAGE.query(if_query).captures(tree_node)
    num_if_stmts = len(if_stmts)
    if num_if_stmts not in {0, 1}:
        raise ParserError(
            f"Only zero or one if statements are supported, but found {num_if_stmts} if statements"
        )

    if len(if_stmts) > 0:
        if_conditions = LANGUAGE.query(if_condition_query).captures(tree_node)
        if_then_stmts = LANGUAGE.query(if_then_query).captures(tree_node)
        if_else_stmts = LANGUAGE.query(if_else_query).captures(tree_node)

        if len(if_conditions) != 1:
            raise ParserError(
                f"Expected one if condition, but found {len(if_conditions)}"
            )
        print(f"If condition: {_capture_to_text(if_conditions[0])}")

        if len(if_then_stmts) != 1:
            raise ParserError(
                f"Expected one if then statement, but found {len(if_then_stmts)}"
            )
        print(f"If then statement: {_capture_to_text(if_then_stmts[0])}")

        if len(if_else_stmts) == 0:
            # In this case we just extract the if then statement
            tree = build_expression_tree(if_then_stmts[0][0])
            inorder_expression = preorder_traversal(tree)
            print(inorder_expression)
            return
        elif len(if_else_stmts) == 1:
            tree = build_expression_tree(if_stmts[0][0])
            inorder_expression = preorder_traversal(tree)
            print(inorder_expression)
        else:
            raise ParserError(
                f"Expected zero or one right statement, but found {len(if_else_stmts)}"
            )

    # Check if tree node loop body has compound statements (e.g. sum += a[i] * a[i];)
    compound_stmts = LANGUAGE.query(body_compound_query).captures(tree_node)

    if len(compound_stmts) not in {0, 1, 2}:
        raise ParserError(
            f"Expected zero or one compound statement, but found {len(compound_stmts)}"
        )

    if len(compound_stmts) > 0:
        # If there are compound statements for different loops, we only consider the innermost loop
        inner_most_compound = compound_stmts[0]
        print(f"Compound statement: {_capture_to_text(inner_most_compound)}")
        tree = build_expression_tree(inner_most_compound[0])
        inorder_expression = preorder_traversal(tree)
        print(inorder_expression)

    # Check if tree node loop body has push statements (e.g. out.push_back(curr);)
    push_stmts = LANGUAGE.query(body_push_query).captures(tree_node)
    num_push_stmts = len(push_stmts)
    if num_push_stmts not in {0, 1, 2}:
        raise ParserError(f"Expected <= 2 push statements, but found {len(push_stmts)}")

    if num_push_stmts > 0:
        for i in range(num_push_stmts):
            print(f"Push statement: {_capture_to_text(push_stmts[i])}")
            tree = build_expression_tree(push_stmts[i][0])
            inorder_expression = preorder_traversal(tree)
            print(inorder_expression)

    # Check if tree node loop body has declaration statements
    captures = LANGUAGE.query(body_decl_query).captures(tree_node)
    print(f"len of decl captures: {len(captures)}")
    if len(captures) > 0:
        for i in range(len(captures)):
            print(f"converting expression: {captures[i][0].text.decode()}")
            tree = build_expression_tree(captures[i][0])
            # print(tree)
            inorder_expression = preorder_traversal(tree)
            print(inorder_expression)


if __name__ == "__main__":
    # Set up some global variables / paths

    # reading arguments from the command line
    # parser = argparse.ArgumentParser()
    # parser.add_argument("--file-path", type=str)
    # args = parser.parse_args()

    # # First we find the source code
    # with open(args.file_path) as f:
    #     source_code = f.read()

    # print("Attempting to parse the following code:")
    # print(source_code)
    # tree = parser.parse(source_code.encode())
    tree = PARSER.parse(example9.encode())
    root_node = tree.root_node
    find_compute(root_node)
