""" 
Preprocessor for converting phosphorus language to correct python code in two steps:

replace_elements -- text converter replacing any special φ code with valid python
ValWrapper       -- ast converter to wrap certain nodes with conversions to φ objects

"""
from IPython.core.latex_symbols import latex_symbols
import re, ast, itertools
from .phival import *
from .parse import Span, Token, STRING, NAME, printerr

escapes={
        ('in',  '∈', ' in '), ("'", 'ʼ', "ʼ"), ("`", 'ʼ', "ʼ"),
        ('->', '⟶', '>>'), #todo: make this >> and overload PhiVal's to form pairs on >>
        ('<',   '⟨', '['), ('>',   '⟩', ']'), 
        ('cup', '∪', '|'), ('cap', '∩', '&'),
        ('vee', '∨', '|'), ('v', '∨', '|'), ('wedge', '∧', '&'), ('^', '∧', '&'),
        ('lnot', '¬', '~'), ('~', '¬', '~'), 
        ('[',   '⟦', 'interpret('),  (']',   '⟧', ')'), 
        ('forall', '∀', '∀'), #('',    'λ', 'lambda '),
        ('hat', '\u0302', '\u0302'), ('bar', '\u0304', '\u0304'),
        #('',    '..', '>>'),       #Hack for ellipsis ranges: treat as binary shift
        #('',    '...', '>>'),      #(which we don't need) and catch in ast transformer
        ('tree', '🌲', 'tree'),
        ('empty', '∅', 'set()')
    }
r"""Contains triples: (completion command, completion value, python value)

completion command -- type backslash ('\'), followed by this code, followed by tab to return:
completion value   -- what gets replaced after hitting tab; the phosphorus preprocessor converts to:
python value       -- a valid python token converted by the completion value
"""

subs=[
    #(r'lambda([^:.]*)[:.]', r'lambda\1:'), # allow .'s instead of :'s after lambda
    (r'rule +([^ :]+):? +⟦?([^⟧]+)⟧? *(?:=>?|->) *(.+) \|\| +(.+)(?=\n)', r"Rule(\1, \2, '\3 if \4 else None')"),
    (r'rule +([^ :]+):? +⟦?([^⟧]+)⟧? *(?:=>?|->) *([^\n]+)(?=\n)', r"Rule(\1, \2, '\3')"),
    (r'^lex\s*([^=\s\.].*?)\s*[=\s:]\s*(.+)', r'lex.update({"""\1""" : \2})'),
    (r'\.\.\.?', r'<<'), #Hack to pick up ellipsis ranges: ValWrappers subs for << TODO: overload PhiVal's for <<
]
""" Contains pairs: (regular expression, replacement string)
    Note: these are replaced at the very start, everywhere in the input, including
        in strings, comments, etc. 
"""

phi_names = {"TreeVal","LambdaVal", "interpret", "Rule", "SemEntity", "SemLiteral", "SemPredicate", "Span"}
compile_time_names = set(globals()['__builtins__'].keys())
compile_time_names.update(phi_names)
#Note: important to not bury run_time_names inside a function call, since these are different in different contexts (especially locals(), I think)
run_time_names = ast.parse('{**locals(), **globals(), **__builtins__.__dict__}', mode="eval").body
""" Lists of python names NOT to convert to PhiVals """
    

def replace_tree(n, item, parent):
    """ Replaces one tree notation in span parent. Both item and the [ ] span after it
        will be replaced. (Note that this involves altering a list while we are 
        processing it -- kosher??)
    """
    
    if item.string != "tree": return False #Trees start with "tree"
    try: 
        tree = parent[n+1]
        #Also check that the next item is a [ ] span, so we can use the word tree elsewhere:
        if not isinstance(tree,Span) or tree[0].string != '[': return False 
    except IndexError: return false #Don't replace "tree" at the end
    
    tree = tree[1:-1] #ignore [ ]
    enum = enumerate(tree)
    for m, child in enum:
        #Insert the word "tree" before [ ]  spans without commas
        if isinstance(child, Span) and child[0].string == '[' \
                and all([t.string != "," for t in child]):
            child = Token(STRING, "tree"); tree.insert(m, child)
        _replace(m, child, tree) #Replace children
    
    del parent[n+1] #delete the original tree notation
    children = str(tree)[1:-1]  #string value of list without brackets: will have commas!
                                #NOTE: must put multi-token chilren in parens
    
    #Replace the word "tree" with the appropriate TreeVal call
    parent[n] = Token(STRING, f'TreeVal({children})', item.spacebefore)
    #print(parent[n])
    return True
    
    
def replace_lambda(n, lam, parent):
    """ Replaces one phosphorus lambda notation in span parent. lam is the delimited Span
        containing the lambda function. Note that Span.parse will ignore substitutions
        in lambda spans to preserve original phosphorus code for printing.
    """
    if lam.type != "lambda": return False
    parent[n] = Token(STRING, f'LambdaVal.parse("""{lam}""")', lam.spacebefore)
    #print(f"Replaced lambda: {lam} with '{lam.spacebefore}' before")
    return True

def replace_comprehension(n, comp, parent):
    """ Replaces a phosphorus-style comprehension with a python comprehension.
        Phosphorus allows using "|" and "," instead of "for" and "if". This function
        figures out which should be "for" and which should be "if", although at least
        one must be "|". Note that other uses of "|" "," and "∈" or "in" must be in
        parens: (a | b) (x,y) (x ∈ D) .
    """
        
    if not isinstance(comp, Span): return False
    try:
        bar = [item.string for item in comp].index('|') # Make sure there's a | ...
        #... and an "in" at the beginning
        intoken = comp[bar+2].string.strip()
        if intoken != 'in' and intoken != '∈': return False 
    except (IndexError,ValueError): return False

    last = None
    for n,item in enumerate(comp):
        _replace(n, item, comp) # Do replacements on children
        
        if not item.string: continue
        s = item.string.strip()        
        if s == 'in': 
            #When we reach an "in" at the top level, the previous separator is "for"
            if last: last.string = ' for '
            last = None 
        elif s == ',' or s == '|':
            #If we reach a new separator, the previous is "if"
            if last: last.string = ' if '
            last = item
            
    if last: #had a , or | at the end with no 'in' after
        if comp[-2] == last: del comp[-2] #Delete trailing ,'s and |'s
        else: last.string = ' if '
    return True

def replace_lex(n, item, parent):
    if item.string != "`": return False
    arg = parent[n+1]
    if isinstance(arg, Span): #call _replace on children of Span
        for n2, item2 in enumerate(arg):
            _replace(n2,item2,arg)
    elif arg.type == NAME:
        arg.type = STRING
        arg.string = f'''"""{arg.string}"""'''
            
    span = Span("[]")[0] #parse creates span within a span
    span.insert(1,arg)
    #print("replaced arg in lex", span.debugstr(), "arg was", arg.debugstr())
    parent[n].string = "lex"
    parent[n].type = NAME
    parent[n+1] = span
    
    return True

def _replace(n, item, parent):
    """ Internal version of replace: checks for replacing our special notations.
        Otherwise, recursively checks other Spans.
    """
    if (replace_lambda(n, item, parent) or replace_comprehension(n, item, parent) 
            or replace_tree(n,item,parent) or replace_lex(n,item,parent)): 
        return
    if isinstance(item,Span):
        replace(item)

escape_dict = {orig : repl for _,orig,repl in escapes}
""" Turns escape substitutions into a replacement dictionary """
def replace(s):
    """ Toplevel Span-replacement function. Tokenizes s and runs internal _replace
    """
    if isinstance(s,str):
        try:
            #print("Replacing in " + s + "\n\n")
            root = Span.parse(s, subs=escape_dict) #parse with string subs
        except Exception as e:
            printerr(e, f"parsing {s}")
            return s
    else: root = s
    
    for n, item in enumerate(root):
        _replace(n,item,root)
    #print("Replaced lambdas: " + str(root) + "|")
    return str(root)

#TODO: ending delimiter can be first character in line
def combine_multiline(lines):
    """ Passes through a list of strings and combines multi-line statements into
        single strings
    """
    new_lines = []
    for line in lines:
        if new_lines and line.startswith(' '):
            new_lines[-1] += line
        else:
            new_lines.append(line)
    return new_lines

def replace_elements(lines):
    """ Replace all special φ notation with valid python code for parsing """
    new_lines = []
    lines = combine_multiline(lines)
    for line in lines:
        for pattern,repl in subs:
            line = re.sub(pattern,repl,line)
        if line.lstrip().startswith('%'): new_lines.append(line)  #ignore jupyter magic command lines
        else:
            new_lines.append(replace(line))
    debug_transform_print("Transformed to:", new_lines)
    return new_lines

def ellipsis(fr, to):
    strs = False
    if isinstance(fr,str): 
        fr = ord(fr)
        strs = True
    if isinstance(to,str):
        to = ord(to)
        strs = True
        
    return [chr(x) if strs else x for x in range(fr,to+1)]

class ValWrapper(ast.NodeTransformer):
    """Wraps certain items in a call to φ(), replaces ranges"""
    
    def wrap(self,node):
        #print("wrapping ", ast.dump(node))
        node = self.generic_visit(node)
        return ast.Call(func=ast.Name(id='φ', ctx=ast.Load()), 
                        args=[node], keywords=[])

    visit_Set = visit_SetComp = visit_Dict = visit_Constant \
        = visit_Num = visit_Str  \
        = visit_ListComp = visit_Call = wrap

    def visit_Call(self, node):
        #print(f"Visiting {ast.dump(node)}")
        if hasattr(node.func, "id") and node.func.id in phi_names:
            #print(f"Found {node.func.id}")
            return self.generic_visit(node)
        return self.wrap(node)
    
    def visit_Tuple(self, node):
        #print("visiting tuple", ast.dump(node))
        return node if isinstance(node.ctx, ast.Store) else self.wrap(node)    
    
    visit_Attribute = visit_List = visit_Tuple #= visit_Starred
    
    def visit_Subscript(self,node):
        if isinstance(node.ctx, ast.Store):
            node = self.generic_visit(node)
            return node
        return self.wrap(node)
    
    # This is the ONLY way to do this. The run_time_names must be evaluated at the same level as 
    # the name itself in order to catch names only defined inside some block like a comprehension
    def visit_Name(self, node):
        #print("visiting", node.id, "In compile_time_names", node.id in compile_time_names)
        if node.id not in compile_time_names and isinstance(node.ctx, ast.Load):
            out = ast.IfExp(test=ast.Compare(left=ast.Str(s=node.id), ops=[ast.In()],
                                             comparators=[run_time_names]), 
                            body=node, orelse=self.wrap(ast.Str(s=node.id)))
            #display(ast.dump(out))
            return out
        return node

    #Just for debugging purposes
    def visit_Expr(self,node):
        try:                
            newnode = self.generic_visit(node)
            if hasattr(node,"value"):
                debug_transform_print("Original Expr: ", ast.dump(node.value))
            if hasattr(newnode, "value"):
                debug_transform_print("Transformed Expr: ", ast.dump(newnode.value))
            #node.value = self.wrap(node.value)
            return newnode
        except:
            return self.generic_visit(node)
    
    #increase precedence of prefix + in function call TODO remove?
    def visit_UnaryOp(self,node):
        if  not isinstance(node.op, ast.UAdd) or \
            not isinstance(node.operand, ast.Call): 
            return self.wrap(node)
        out = ast.Call(func=ast.UnaryOp(op=ast.UAdd(),operand=node.operand.func), 
                        args=node.operand.args, keywords=node.operand.keywords)
        out = self.generic_visit(out) #Do this at the end
        return out
    
    def visit_BinOp(self,node):
        #print("Visiting BinOp", ast.dump(node))
        if not isinstance(node.op, ast.LShift): return self.wrap(node)
        # Replace << operator with a starred range (HACK)
        node = self.generic_visit(node)
        return ast.Starred(value=ast.Call(func=ast.Name(id='ellipsis',ctx=ast.Load()), 
            args=[node.left, node.right], keywords=[]), ctx=ast.Load())

ip = get_ipython() #Not entirely sure why this must be a global
def debug_transform_print(*s):
    """ Helper function for debugging transformation """
    try:    debug_transform = ip.ev("debug_transform")
    except: debug_transform = False
    if debug_transform:
        print(*s)
    
#TODO: remove latex symbols & interactivity = all
def unload_ipython_extension(ip):
    # Remove old input transformers:
    for _x in ip.input_transformers_cleanup:
        if hasattr(_x, "__name__") and _x.__name__  == 'replace_elements':
            #print("Removing Input Transformer")
            ip.input_transformers_cleanup.remove(_x)
    #Remove old AST transformer    
    for _x in ip.ast_transformers:
        if isinstance(_x, ValWrapper):
            #print("Removing AST Transformer")
            ip.ast_transformers.remove(_x)
    del _x
    
    
def load_ipython_extension(ip):
    #Ignore SyntaxWarning's that arise since we are not doing pure python
    import warnings
    warnings.simplefilter("ignore")
    
    # Add the new tab completions
    for escape, repl, _ in escapes:
        if escape: latex_symbols['\\' + escape] = repl

    # Add new input transformer
    ip.input_transformers_cleanup.append(replace_elements)
    
    #Add new AST transformer    
    ip.ast_transformers.append(ValWrapper())

    from IPython.core.interactiveshell import InteractiveShell
    InteractiveShell.ast_node_interactivity = "all"
    
    ip.ex("from phosphorus import *; debug_transform = False")

    print(r"""
             _    _                  _    _
            | |  | |                | |  | |
           _| |_ | |__   ___  ___  _| |_ | |__   ___  _ __ _   _  ____
          /     \| '_ \ / _ \/ __|/     \| '_ \ / _ \| '__| | | |/ ___)
         ( (| |) ) | | | (_) \__ ( (| |) ) | | | (_) | |  | |_| ( (__
          \_   _/|_| |_|\___/|___/\_   _/|_| |_|\___/|_|   \__,_|\__ \
            | |                     | |                            _) )
            |_|                     |_|                           (__/

        Welcome to the Phosphorus Meaning Engine v2
        Created by Ezra Keshet (EzraKeshet.com)

    """)
    
if __name__ == "__main__":
    ip = get_ipython()
    load_ipython_extension(ip)