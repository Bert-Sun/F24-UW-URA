# %%
from sage.all import *
import itertools

# %%
P = 3

# constructor to build a sage rational tuple
def qqt(*args):
    return tuple(QQ(arg) for arg in args)

# treat functions x \mapsto upx + d as the tuple (u, d)
# typedef pair<sage.QQ,sage.QQ> edge
# maps = [qqt(1, 1), qqt(1,2), qqt(2,1)]
# maps = [qqt(1, 0), qqt(2, 1), qqt(2, 3)]
maps = [qqt(1,0), qqt(1, 1), qqt(2,3)]

# calculates the composition B^{-1} \circ state \circ A
# where A, B are maps and state is a state as above
# TODO: rewrite to be more readable as in invert_map
def apply_map(B, state, A):
    global P
    u = state[0]*A[0]/B[0]
    d = (state[0]*A[1] + state[1] - B[1])/(P*B[0])
    return qqt(u,d)

# calculates a return state such that 
# apply_map(B, return_state, A) = state
def invert_map(B, state, A):
    global P
    (u_b, d_b) = B
    (u_a, d_a) = A
    (u, d) = state
    u_new = u_b/u_a *u
    d_new = u_b*P*d - u_new*d_a + d_b
    return (u_new, d_new)

# returns if the map is a valid map from \mathbb{Z}_p \to \mathbb{Z}_p
def is_valid(map):
    global P
    # supposing that all affine offsets must have valuation = 1
    if map[1].numerator()%3 == 0: return False
    # assert (map[0] is a unit in \mathbb{Z}_p)
    return (not ZZ(P).divides(map[1].denominator()))

# typedef pair<sage.QQ, sage.QQ> state
class node:
    parents = {}
    children = {} # map< state, vector<edge> >
    s = (0,0)
    def __init__(self, s, parent=None, p_edge=None, child=None, c_edge=None):
        self.s = s
        self.parents = dict()
        self.children = dict()
        if parent:
            self.parents[parent] = [p_edge]
        if child:
            self.children[child] = [c_edge]

    def add_parent(self, parent, p_edge):
        if parent in self.parents.keys():
            if p_edge not in self.parents[parent]:
                self.parents[parent].append(p_edge)
        else: self.parents[parent] = [p_edge]
~
    def add_child(self, child, c_edge):
        if self.children.get(child):
            # append edge if only not already in child list
            if c_edge not in self.children[child]:
                self.children[child].append(c_edge)
        else: self.children[child] = [c_edge]

    def __str__(self):
        return f"parents: {self.parents.__str__()}\n{self.children.__str__()}"
# %%
# to each state assign a "state type" that designates which maps
# are applicable to the state
type_bitmask = dict()
# generate the type bitmask
it = 0
for i,j in itertools.product(range(len(maps)), repeat=2):
    type_bitmask[(i,j)] = 2**it
    it += 1

# given a list of applicable maps, return the type
def get_type_from_maps(applicable_maps):
    state_type = 0
    for map in applicable_maps:
        state_type += type_bitmask[map]
    return state_type

# given a state, find its type
def get_state_type(state):
    global P
    # global maps
    # state_type = 0
    # for i, j in itertools.product(range(len(maps)), repeat=2):
    #     if is_valid(apply_map(maps[i], state, maps[j])):
    #         state_type += type_bitmask[(i,j)]
    # state_type *= 100
    state_type = 100*(state[0]%P**4) + (state[1]%P**4)
    return state_type
# %%
def insert_state_type_transition(type_dict, p_type, edge, c_type):
    # global state_type_transitions
    if type_dict.get(p_type):
        if type_dict[p_type].get(edge):
            # transition already exists
            # expected_child_type = type_dict[p_type][(i,j)]
            # if c_type != expected_child_type:
            #     print("@@ state type fail", p_type, c_type, (i,j), state,
            #           "expected", expected_child_type)
            # if type_dict[p_type][edge].get(c_type):
                type_dict[p_type][edge].add(c_type)
            # else: type_dict[p_type][edge][c_type] = 1
        else: type_dict[p_type][edge] = {c_type}
    else: type_dict[p_type] = {edge: {c_type}}
    
def is_finite_type(maps, initial_state=qqt(1,0), max_states=10000, verbose=False):
    states = {initial_state: node(initial_state)}
    state_type_transitions = dict()
    state_types = {initial_state: get_state_type(initial_state)}
    new_states = {initial_state}
    # store state_type x edge -> state_type
    CALC_INV = False
    is_finite = True
    while len(new_states) > 0:
        state = new_states.pop() # pop a state to transition from
        # loop over all pairs of maps and apply them
        for i, j in itertools.product(range(len(maps)), repeat=2):
            next_state = apply_map(maps[i], state, maps[j])
            state_node = states[state]
            if is_valid(next_state):
                # add child to parent node
                state_node.add_child(next_state, (i,j))
                # if next_state is new node, then add to states
                if next_state not in states.keys():
                    # add to states
                    next_node = node(next_state, state, (i,j))
                    states[next_state] = next_node
                    # add to new_states pqueue
                    new_states.add(next_state)
                    # add state type information
                    state_types[next_state] = get_state_type(next_state)

                # if node already exists then add new parent to it
                else:
                    states[next_state].add_parent(state, (i,j))
                if verbose: print(state, f"--{i},{j}-->", next_state)

                # if the child state is valid, check/insert into type
                # transition table
                parity = state[1]%P
                parent_state_type = state_types[state]
                child_state_type = state_types[next_state]
                insert_state_type_transition(
                    state_type_transitions,
                    parent_state_type, (i,j,parity), child_state_type)
        # calculate inverse states
            if CALC_INV:
                prev_state = invert_map(maps[i], state, maps[j])
                # assert is_valid(prev_state)
                # note that is_valid only checks that the state is a map
                # from Z_p -> Z_p, more complex invariant open set pruning
                # may be possible, but not currently investigated
                if is_valid(prev_state):
                    # if prev is not in list of states, add to it and create 
                    # a node for it, and insert to new_states pqueue
                    if prev_state not in states:
                        prev_node = node(prev_state, child=state_node, c_edge=(i,j))
                        states[prev_state] = prev_node
                        new_states.add(prev_state)
                        state_types[prev_state] = get_state_type(prev_state)
                    # else prev_node already exists, add current state as child
                    else:
                        states[prev_state].add_child(state, (i,j))
                    
                    # add prev_node as a parent to current state
                    state_node.add_parent(prev_state, (i,j))
                    if verbose: print(prev_state, f"--{i},{j}-->", state)

                    # insert into state transition table
                    insert_state_type_transition(
                        state_type_transitions,
                        state_types[prev_state],
                        (i,j,prev_state[1]%P),
                        state_types[state]
                    )

        if len(states) > max_states:
            is_finite = False
            break
    return is_finite, (states, state_types, state_type_transitions)
    
# %%
# treat functions x \mapsto upx + d as the tuple (u, d)
# typedef pair<sage.QQ,sage.QQ> edge
# maps = [qqt(1, 1), qqt(1,2), qqt(2,1)]
maps = [qqt(1, 0), qqt(7, 1), qqt(7, 3)]
# maps = [qqt(1,0), qqt(1, 1), qqt(2,3)]
# maps = [qqt(1,0),qqt(1,1),qqt(2,1),qqt(4,1)]
# maps = [qqt(1,0), qqt(1,1)]

# %%
# treat state maps ux + d as the tuple (u, d)
# by equicontractiveness of above p cancels out
# map<state, node> 
initial_state = qqt(1, 0)
finiteness, (states, state_types, state_type_transitions) = is_finite_type(maps, initial_state=initial_state, max_states=10000, verbose=True)
print(finiteness)

# %%
# utility cells for reused code snippets to browse tree structure
owo = []
for state in states.keys():
    if state[1].denominator() > 1024 and state[0] == 1:
        owo.append(state)
# %%
# backtrack parents of a state
state = qqt(4, 395/512)
visited = set()
state_list = []
# init state list
for parent in states[state].parents.keys():
    state_list.append(parent)
    print(parent, states[state].parents[parent])
    visited.add(parent)

# %%
# print(state_list)
new_state_list = []
for state in state_list:
    print("--- at state ---", state)
    for parent in states[state].parents.keys():
        if parent not in visited:
            new_state_list.append(parent)
            visited.add(parent)
            print(parent, states[state].parents[parent])
        else: print("visited", parent, states[state].parents[parent])
state_list = new_state_list.copy()


# %%
states_by_types = dict()
for state in states.keys():
    state_type = state_types[state]
    if states_by_types.get(state_type):
        states_by_types[state_type].append(state)
    else: states_by_types[state_type] = [state]

# %%
def to_base_p(n):
    global P
    if n == 0: return 0
    ret = ""
    while n > 0:
        ret += str(n%P)
        n //= P
    return ret[::1]