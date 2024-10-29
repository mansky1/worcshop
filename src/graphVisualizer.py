import graphviz
import re, os

# Example text containing Coq proof structure
text = """semax Delta
  (PROP ( )
    LOCAL (temp _b (Vint (Int.repr 3));
    temp _a (Vint (Int.repr 5)); 
    gvars gv)  SEP (listrep s1 w; data_at Tsh t_struct_list (h, y) v; listrep r y)) SEP (has_ext tt)) 
  (((_t'1 = _add([(_a)%expr; (_b)%expr]);
     _result_add = _t'1;)
    _t'2 = _slow_add([(_a)%expr; (_b)%expr]);
    _result_slow_add = _t'2;)
MORE_COMMANDS) POSTCONDITION"""

class GraphVisualizer:
    def __init__(self, output_folder="output"):
        # Ensure output folder exists
        os.makedirs(output_folder, exist_ok=True)
        # Initialize graph for Coq proof visualization, specifying path to save in output_folder
        self.graph = graphviz.Digraph('proof_graph', 
                                      filename=os.path.join(output_folder, "proof_visualization"),
                                      node_attr={'shape': 'box'})
        self.graph.attr(rankdir='LR', splines="curved", fontname="Arial")

    def add_node(self, name, label, shape="box", color="lightgrey"):
        # Add a single node with specified properties
        self.graph.node(name=name, label=label, shape=shape, style='filled', fillcolor=color)

    def add_edge(self, source, destination, color="black"):
        # Add an edge between two nodes in the graph
        self.graph.edge(source, destination, color=color)

    def visualize_pointer_relationship(self, source_pointer, destination_pointer):
        # Visualizes relationship between a source and destination
        self.add_node(source_pointer, source_pointer, shape="ellipse", color="lightblue")
        self.add_node(destination_pointer, destination_pointer, shape="ellipse", color="lightblue")
        self.add_edge(source_pointer, destination_pointer, color="darkgreen")

    def create_subgraph(self, source_pointer, values):
        # Creates a subgraph for multiple values pointing to a head value
        with self.graph.subgraph(name="cluster_1") as cluster:
            cluster.attr(color="black", penwidth="2", nodesep="0.3", margin="8")
            head_value = values[0]  # Define head for edge connection
            for value in values:
                cluster.node(value, shape="square", style='filled', fillcolor='lightblue')
            self.add_edge(source_pointer, head_value, color="darkorange")

    def render_graph(self):
        # Render graph and open for viewing
        self.graph.render(view=True)

def extract_variables(pattern, text):
    # Extracts content from proof text based on a pattern
    match = re.search(pattern, text, re.DOTALL)
    variable_list = []
    if match:
        # Retrieve the content inside parentheses and split by semicolon
        content = match.group(1)
        variable_list = content.split(';')

    return variable_list

def extract_variable_values(pattern, variable_list):
    # Extracts names and values from a list of variables
    variable_values = []
    for variable in variable_list:
        variable = variable.strip()
        match = re.match(pattern, variable, re.DOTALL)
        if match:
            parts = match.group(1).split(' ')
            name, value = parts[0], parts[-1].replace(')', '')
            variable_values.append((name, value))
    return variable_values


def generate_proof_graph(text):
    # Initialize graph visualizer
    graph_visualizer = GraphVisualizer()

    # Regex patterns
    local_pattern = r'LOCAL\s+\((.*)\)\s+SEP'
    temp_var_pattern = r'temp (.*)'
    sep_pattern = r'SEP\s+\((.*?)\)\)'

    # Extract local variables
    local_variables = extract_variables(local_pattern, text)
    if local_variables:
        variable_values = extract_variable_values(temp_var_pattern, local_variables)
        label_list = [f"{name} : {value}" for name, value in variable_values]
        label_text = '<Local Temp Variables:<BR/>' + '<BR/>'.join(label_list) + '>'
    else:
        label_text = '<no Temp Variables>'
    graph_visualizer.add_node(name='local_vars', label=label_text)

    # Extract and visualize SEP clause pointer relationships
    sep_variables = extract_variables(sep_pattern, text)
    pointer_keyword = 'listrep'
    if sep_variables:
        for variable in sep_variables:
            variable_items = variable.strip().split(' ')
            source_pointer = variable_items[-1]  # Last item is the source pointer

            if pointer_keyword in variable:
                destination_pointer = variable_items[1]  # Second item is the destination pointer
                graph_visualizer.visualize_pointer_relationship(source_pointer, destination_pointer)
            else:
                # Handle pointers inside parentheses
                match = re.search(r'\((.*)\)', variable, re.DOTALL)
                if match:
                    values = match.group(1).replace(' ', '').split(',')
                    graph_visualizer.create_subgraph(source_pointer, values)

    # Render the final graph
    graph_visualizer.render_graph()

if __name__ == "__main__":
    generate_proof_graph(text)