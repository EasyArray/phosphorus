""" Defines various kinds of PhiVals for storing Phosphorus Values """
from graphviz import Graph
from numbers import Number
import builtins; import ast
import re; import time

from .parse import Span, errors_on, log, debugging

ip = get_ipython()
""" ip is the ipython object, provides useful methods """
rules = {}
""" stores our interpretation rules """

class Lex(dict):
    def __missing__(self, key):
        return key
    
    def update(self, *args, **kwargs):
        global memo
        memo = {} #redo memoization if you update the lexicon
        print(f"Updating the global lexicon 'lex' to include {args[0]}")
        super().update(*args, **kwargs)

lex = Lex()
""" stores our lexicon """


# NOTE: the other form of greek letter phi doesn't work for some reason!
def φ(*args, literal=False, **kwargs):
    """ The main function to convert user input to a PhiVal """
#     if len(args) > 1:
#         return TreeVal(*args, **kwargs)
    
    input = args[0]
    #print("applying φ to " + str(args[0]))
    if isinstance(input, Span):
        return SpanVal(input)
    if isinstance(input, PhiVal): 
        #print("Found PhiVal", input)
        return input
    if isinstance(input, bool): return input
    if isinstance(input, Number): return NumVal(input)
    if isinstance(input, set): return SetVal(map(φ,input))
    if isinstance(input, frozenset): return SetVal(map(φ,input))
    if isinstance(input, dict) and not len(input): return SetVal(set())
    if isinstance(input, list): return TupleVal(map(φ,input))
    if isinstance(input, tuple): return TupleVal(map(φ,input))
    if isinstance(input, str): return ConstantVal(input)

    return input

# global state variable for whether parsing should be shown
parseon = False
# memo is a dictionary mapping inputs to [dictionaries that map bindings
# to the corresponding output and rule used to achieve that output]
# That is, memo: [input -> [binding -> (output, rule used)]]
memo = dict()
def interpret(x, showparse=None, memoize=True, raise_errors=False, print_errors=True, **kwargs):
    global parseon, memo
    # tuple of bindings coming from kwargs, used for memoization
    bindings = tuple(kwargs.items())

    # set state of parseon to showparse so that any recursive
    # calls that happen inherit the value of showparse
    if showparse is not None:
        oldparse = parseon
        parseon = showparse
        # when memo is used, the parsing is never shown. So,
        # when parsing should be shown, memo is reset so that
        # everything gets computed by hand
        if showparse and memoize:
            memo = dict()

    # try/finally so that parseon state will always be reset at the end
    try:
        out = None # will be the output of a rule applied to x
        r   = None # will be the rule applied to x
        
        # try to use memoization to avoid recomputing
        if memoize and x in memo and bindings in memo[x]:
            out, r = memo[x][bindings]
        # if the previous if clause didn't happen, we need to compute the interpretation
        else:
            # get all results of applying rules to x
            results   = [(r, rules[r].run(x, **kwargs)) for r in rules]
            outputs   = [o for (_,o) in results if o is not None]
            rulesused = [r for (r,o) in results if o is not None]

            # if there are no interpretations, raise an error
            if not outputs:
                raise ValueError(f"{str(x)} is not interpretable")
            # if there is more than one interpretation, raise an error
            elif len(outputs) > 1 and not isinstance(outputs, Span):
                raise ValueError(f"{str(x)} has multiple interpretations")

            out, r = outputs[0], rulesused[0]
        
        # show parsing if output was actually computed
        if parseon and not (memoize and x in memo):
            from IPython.display import display_html
            try: res = out._repr_html_()
            except: res = out
            display_html(f"<span style='float:right; font-family:monospace'>(by {r})</span>"
                         f"<span style='margin-left: 40px'>⟦{x},{kwargs}⟧ = {res}</span>", raw=True)
    
    # don't raise ValueErrors if raise_errors is turned off
    except ValueError as e:
        if print_errors: print(f"ERROR: {e}")
        if raise_errors: raise e
        out = None
    finally:
        # set state of parseon back to what it was before this call
        if showparse is not None:
            parseon = oldparse
    
    # save values for future
    if memoize:
        if x in memo:
            memo[x][bindings] = (out, r)
        else:
            memo[x] = {bindings: (out, r)}
    
    return out

def ensurelist(x):
    """ If x is not already a list or set, returns a list containing only x.
        If x is already a list or set, returns x.
    """
    return x if isinstance(x, (frozenset, set, list, tuple)) else [x]

def step(x, n=1, accum=False, showrules=False, **kwargs):
    """ Similar to interpret, but for basic formal systems like MIU.
        Finds all outputs after applying rules to x at most n times.
        If accum == False: only finds outputs after exactly n rule applications
        If showrules == True: prints out the rules being applid and the
                              resulting outputs at each step.
    """
    # outputs is a list of sets
    # outputs[i] is the set of outputs after n steps
    outputs = []
    outputs.append(set(ensurelist(x))) # after 0 steps, x is the only output

    for i in range(n):
        # for output printing, keep a dict of (input, rule) -> rule applied to input
        # inputs come from outputs of the previous step
        newresults = dict()
        for y in outputs[-1]:
            for r in rules:
                newresults[(y,r)] = rules[r].run(y, **kwargs)
        newresults = dict(filter(lambda pair: pair[1] is not None, newresults.items()))

        if showrules:
            from IPython.display import display_html
            if n == 1:
                display_html(f"<span style='width:100%; border-bottom-style:solid; border-bottom-width:thin; display:inline-block; font-weight:bold;'>Applying All Rules</span>", raw=True)
            if n > 1:
                display_html(f"<span style='width:100%; border-bottom-style:solid; border-bottom-width:thin; display:inline-block; font-weight:bold;'>Step {i + 1}</span>", raw=True)
            for y,r in newresults:
                 display_html(f"<span style='float:right; font-family:monospace'>(by {r})</span>"
                              f"<span>{y} &rightarrow; {newresults[(y,r)]}</span>", raw=True)
        
        newoutputs = set()
        for p in newresults:
            newoutputs.update(newresults[p])
        
        # old steps are only needed if accumulating
        if not accum:
            outputs.pop(0)
        outputs.append(newoutputs)

        # display current list of results
        """ removed this to be consistent with showparse style in interpret
        if showrules:
            print(f"Current values: {set.union(*outputs) if accum else outputs[-1]}")
        """
    
    # outputs is now a list of sets of outputs at each step
    final = []
    for S in outputs:
        final.extend(S)
    return final

def repeat(f,x,n,accum=False):
    """ Recursively applies f to x, n times.
        If accum == False: returns the value of f(f(f(...f(x))))
        If accum == True:  returns a list with each application:
                           [x, f(x), f(f(x)), ..., f(f(f(...f(x))))]
    """
    for _ in range(n):
        x = ensurelist(x) + ensurelist(f(x)) if accum else f(x)
    return x

class PhiVal(object):
    """ Base class for phosphorus objects """
    def parts(self): return iter(list(self))
    
    #TODO: allow multiple matches, like matches does now
    def match(self, target, variables=frozenset()):
        #print("PhiVal match 1", self, target, variables)
        if self.is_variable(variables): return {self:target}
        if self == target:              return {}
        #print("PhiVal match", self, target, variables)
        try:
#            if len(self) == 1: return None   # Not sure why this was here
            if len(target) != len(self): return None
            bindings = {}
            for s,t in zip(self,target):
                bs = s.match(t,variables)
                if not safe_update(bindings, bs): return None
            return bindings
        except:
            return None
                
    def is_variable(self, variables=[]):
        try: return self in variables
        except: return False

    def type(self): return "ϕ"
    #def semtype(self): = type

    def _repr_html_(self):
        if hasattr(self,"_repr_svg_"):
            out = self._repr_svg_()
        else:
            from html import escape
            out = escape(f"{repr(self)}")
            
        stype = SemType.type(self)
        if stype:
            stype = repr(stype).replace(' ', '')
            out += ("<span style='float:right; font-family:monospace; font-weight:bold; background-color:#e7ffe5; color:black;'>"
                    f"∈{stype}</span>")
        out += ("<span style='float:right; font-family:monospace; font-weight:bold; background-color:#e5e5ff; color:black;'>"
                f"{self.type()}</span>")
        return out
            
    
    #FIX: circular import here; reevaluate after more is written
    def __call__(self,*args):
        from .semval import SemLiteral
        out = repr(self) + "(" + ','.join(repr(a) for a in args) + ")"
        out = SemLiteral(out)
        #print("PhiVal call of "); display(out)
        return out
    
    def __eq__(self, other):
        return repr(self) == repr(other)
    
    def __rshift__(self,other):
        return [self,other]
    
    def __matmul__(self,other):
        """Overloads the @ matrix multiplication operator for pattern matching: 

        target @ pattern returns the bindings generated (or None if there's no match)"""
        return other.match(self)

    def update(self, bindings):
        #print("super update", self)
        if self in bindings: return bindings[self]
        try:
            up = [x.update(bindings) for x in self]
            return type(self)(up)
        except:
            return self
        
class LambdaVal(PhiVal):
    def __init__(self, args, body, guard=None, env={}):
        self.args = args; self.body = body; self.guard = guard; self.env = env
        self.stype = None
        
    def __repr__(self):
        #print("Lambda body " + self.sub())
        err_status = errors_on(False) #suppress errors when printing out
        out = "[λ" + ", ".join(map(str,self.args))
        if self.guard is not None: out += f": {self.guard.update(self.env)}"
        out += "." + self.sub() + "]" #str(eval_n(self.sub())) + "]"
        errors_on(err_status)
        return out
    
    def __call__(self, *args, **kwargs):
        def mylog(s): log(s,"LambdaVal.__call__")
        if kwargs:
            [kwargs.pop(arg,"") for arg in self.args]
            return LambdaVal(self.args, self.body, self.guard, {**self.env, **kwargs})
        
        # TODO: mesh with "sub" function below?
        bindings = {**self.env} #Copy the env dictionary
        bindings.update(dict(zip(self.args, args)))
        mylog("LambdaVal call with body " + str(self.body) + " bindings: " + str(bindings))

#        if SemType.type(args[0]) != self.semtype()[0]:
#            raise ValueError(f"{args[0]} is wrong type; should be {self.semtype()[0]}")
        
        if self.guard is not None:
            s = self.guard.update(bindings)
            mylog(f"Checking guard {s}")
            out = s.ev_n()
            mylog(f"Checking guard {s}\nGot output {out}::{type(out)}")
            if isinstance(out, Span) or not out:
                raise ValueError(f"Not in the domain: {args}")
        
        s = self.body.update(bindings) #self.sub(bindings)
        mylog("Lambda output: " + s.debugstr() + " Evaled " + str(s.ev_n()))
        out = s.ev_n()     
        # TODO: catch ValueErrors about domain internally, but still return spans for others?
        return out

    def parse(span):
        if isinstance(span,str): span = Span.parse(span.strip())[0]
        g = iter(span)
        delim = next(g)
        if not delim.isopendelim(): 
            raise SyntaxError("Strange delimiter for lambda " + delim)
        curr = next(g)
        if curr.string != "λ": 
            raise SyntaxError("Incorrect operator for lambda" + curr.string)
        arg = next(g)
        if not arg.isvariable(): 
            raise SyntaxError(f"Incorrect variable: {arg.string} with token type {arg.type}")
        arg = arg.string
        curr = next(g).string
        from .semval import SemVar
        if curr == "∈" or curr == "/":
            curr = next(g)
            t = SemType.parse(curr)
            arg = SemVar(arg,t)
            curr = next(g).string
        else: 
            arg = SemVar(arg,ConstantVal("e"))
        guard = None
        if curr == ":":
            guard = Span()
            for curr in g:
                if curr.string == ".": curr = "."; break
                guard.append(curr)
        elif curr != ".": raise SyntaxError("Stray item before . in lambda: " + curr)
        
        body = Span()
        for curr in g:
            if curr.isdelim(): break
            body.append(curr)
        
        return LambdaVal((arg,), body, guard) 
        #return f'LambdaVal(("""{arg}""",),"""{str(body).lstrip()}""","""{guard}""")'
    
    def sub(self, bindings={}):
        subs = {**self.env}
        subs.update(bindings)
        return str(self.body.update(subs))
        
    def semtype(self):
        if not self.stype:
            err_status = errors_on(False) #suppress errors while calculating type TODO: use with
            try:
                ta = τ(self.args[0])
                #print("Type of " + self.args[0] + " is " + str(ta))
                ta = ta if ta != None and ta != "constant" else ConstantVal("e")
                #out = τ(self())
                out = τ(self.body.ev_n()) #bypass the guard for type purposes
                #print(f"Type of {self()} is {out}")
                out = ConstantVal("t") if out=="constant" else out
                out = TupleVal([ta,out])
            except Exception as e:
                print(type(e).__name__, "in semtype():", e)
                out = TupleVal([ConstantVal("e"),ConstantVal("t")])
            errors_on(err_status)
            self.stype = out
            
        return self.stype

    def type(self):
        return "λ"
        
class NumVal(int,PhiVal):
#  def __repr__(self):
#    if self.is_integer(): return str(int(self))
#    return self

    def type(self):
        return "number"

    def __rshift__(self,other):
        return [self,other]


class SetVal(frozenset,PhiVal):
    def __call__(self,*args):
        """ Treats self as a function and applies the function to args.
            - If self represents a function (i.e., all elements are pairs),
              then applies the represented function to args. If there are
              multiple possible outputs, return a list of all of them.
            - Otherwise, treats self as an characteristic function, true
              of the set's members.
        """
        if len(args) == 0: return self
        if len(args) == 1:
            x = args[0]
            #NOTE: this condition prevents SetVals from being functions that
            #      take tuples as inputs, but means that if a tuple is passed
            #      to a SetVal representing a function, the indicator function
            #      of the underlying set is used instead.
            if not isinstance(x,tuple) and \
               all(isinstance(y,tuple) and len(y)==2 for y in self):
                try:
                    out = [y[1] for y in self if y[0] == x]
                except:
                    return 1 if x in self else 0
                else:
                    if not out: raise ValueError(f"{x} is not in the domain of {self}")
                    if len(out) == 1: out = out[0]
                    return out
            else:
                return 1 if x in self else 0
        return 1 if args in self else 0
    
    def __getitem__(self,x):
        return x in self

    def __repr__(self):
        if not len(self): return '∅'
        return "{" + ", ".join(sorted(map(str, self))) + "}"
    
    def __add__(self,other):
        asdict = dict(self)
        asdict.update([other])
        return SetVal(asdict.items())

    def type(self):
        return "{}"

    #Todo: allow different mappings of variables
    def match(self, target, variables=[]):
        #print("SetVal match:", self, target, variables)
        bindings = super().match(target, variables)
        if bindings is not None: return bindings
        bindings = {}
        svars = [x for x in self if x.is_variable(variables)]
        srest = [x for x in self if x not in svars]
        for t in target:
            try: srest.remove(t)
            except:
                try:
                    var = svars.remove(t) if t in svars else svars.pop()
                    if not safe_update(bindings, {var : t}): return None
                except:
                    return None
        return bindings
            

class TupleVal(tuple, PhiVal):
    def __repr__(self):
        return "⟨" + repr(list(self))[1:-1] + "⟩"
    
    def type(self):
        return "⟨⟩"

class SpanVal(PhiVal): #Todo inherit from span? Messes up printing?
    def __init__(self, span=Span()):
        if not isinstance(span, Span):
            span = Span.parse(span)
        self.span = span
            
    def type(self):
        return "code"
    
    def semtype(self):
        return ConstantVal("t")
    
    def __repr__(self):
        return str(self.span)
        #return repr(self.span)

    def __bool__(self):
        return bool(self.span)
    
    def debugstr(self):
        return self.span.debugstr()
    
    def update(self,b):
        return self.span.update(b)

    def ev(self, print_errors=True, throw_errors=False):
        return self.span.ev(self, print_errors, throw_errors)

    def ev_n(self, count=100, print_errors = True, throw_errors = False):
        return self.span.ev_n(self, count, print_errors, throw_errors)
    
class TreeVal(tuple, PhiVal):
    def __new__(cls, *children):
        if len(children) == 1 and isinstance(children[0], list):
            children = children[0]
        
        name = ""
        try:
            if children[0].startswith("_"):
                name = ConstantVal(children[0][1:])
                children = children[1:]
        except: pass
        instance = super().__new__(cls, children)
        instance.name = ConstantVal(name)
        instance.svg = None
        return instance
        
    def parts(self): return iter([self.name, *self])

    #issue: if whole self is replaced, will still try to replace name
    def update(self, bindings):
        up = super().update(bindings) #headless copy
        up.name = self.name.update(bindings) if self.name else self.name
        return up
        
    def match(self, target, variables=[]):
        #print("TreeVal match", self, target, variables)
        if not hasattr(target, "name"): return None
        if len(self.name) == 0: bindings = {}
        else: bindings = self.name.match(target.name,variables)
        bs = super().match(target, variables)
        #print("Bindings so far:", bs)
        if not safe_update(bindings, bs): return None
        return bindings
        
    def type(self):
        return "tree"

    #TODO: convert to tree[...] notation now that replace_trees can handle internal tree's 
    def __str__(self):
        name = f"_{self.name} " if self.name else ""
        return f"tree[{name}{' '.join([str(x) for x in self])}]"
#         children = (",{}"*len(self)).format(*self)
#         if not name: children = children[1:]
#         return f"TreeVal({name}{children})"
    
    def _repr_svg_(self):
        if self.svg: return self.svg

        out = Graph()
        graph_attr = {
            "fontsize": "12", "label": "", "labelloc": "t", "splines": "line",
            "nodesep": "0.15", "ranksep": "0.15", "margin": "0"}
        out.attr("graph", **graph_attr)

        node_attr = {
            "fontsize": "12", "shape": "plaintext", "height": "0.25", "margin": "0"}
        out.attr("node", **node_attr)

        edge_attr = {
            "headport": "n", "tailport": "s"}
        out.attr("edge", **edge_attr)
        
        def add_node(node, parent=None):
            tree = isinstance(node, TreeVal)
            label = node.name if tree else repr(node)
            label = label.strip() if label else ""

            node_attr = dict()
            if not label: node_attr["height"] = "0"
            out.node(str(id(node)), label, **node_attr)
            
            if parent:
                edge_attr = dict()
                if len(parent) == 1: edge_attr["weight"] = "100"
                out.edge(str(id(parent)), str(id(node)), **edge_attr)
            
            if tree: map(lambda n: add_node(n, node), node)
        
        add_node(self)
        self.svg = out._repr_svg_()
        return self.svg
    
    """ Necessary because Jupyter displays items using repr, not str, and trees
        should be displayed as svgs in the output of cells.
    """
    __repr__ = _repr_svg_
    
    
class ConstantVal(str, PhiVal):
    def parts(self):
        length = len(self)
        return iter([self[i:j] for i in range(length) for j in range(i+1, length+1)])
    
    def match(self, target, variables=[]):
        #print("ConstantVal match 1", self, target, variables)
        bindings = super().match(target,variables)
        if bindings is not None: return bindings
        #print("ConstantVal match", self, target, variables)
        if isinstance(target, str):
            bs = matches(self, target, variables)
            if bs: return bs #bs[0] if len(bs)==1 else bs
        return None
    
    def update(self, bindings):
        #print(f"Updating {self} with bindings {bindings}")
        out = super().update(bindings)
        #print(f"Output is {out} and equals self: {out == self}"); time.sleep(.1)
        if out != self or len(out)<2: return out
        try:
            out = [str(ConstantVal(x).update(bindings)) for x in self]
            return ConstantVal(''.join(out))
        except Exception as e:
            print(f"{type(e).__name__} updating {self}: {e}")
            return self
    
#     def __str__(self):
#         from keyword import iskeyword
#         #s = repr(str(self))[1:-1]
#         s = self
#         return s if (s.isidentifier() and not iskeyword(s)) else "'" + s + "'"
    
    def __repr__(self):
        return repr(str(self))[1:-1]
    
    def type(self):
        return "constant"
    
    def is_variable(self, variables=[]):
        if variables:
            return super().is_variable(variables)
        return len(self)==1 and ord(self) > 909 and ord(self) < 991  #Single Greek letter

    def __pos__(self): #TODO: remove?
        return lex[self]

class SemType(TupleVal):
    D = {
        'e' : ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z'],
        't' : [0,1]
    }
    
    metamarkers = "_ʼ"
    
    # TODO: memoize or otherwise streamline
    def type(x):
        if x is None:
            return ConstantVal('t') # small hack for uninterpretable lambda bodies
        
        from .semval import SemLiteral
        if isinstance(x, SemLiteral): # can't check equality of SemLiterals
            return ConstantVal("t") 

        for t in SemType.D:
            if x in SemType.D[t]: return ConstantVal(t)
            
        if isinstance(x,ConstantVal) and len(x) and x[-1] in SemType.metamarkers:
            return ConstantVal("e")
            
        if isinstance(x,Span):
            return ConstantVal('t')
      
        if hasattr(x, 'semtype'):
            return x.semtype()
        
        return None
    
    def parse(item):
        if not isinstance(item,Span):
            return ConstantVal(item.string)
        
        out = []
        for curr in item:
            if not (curr.isdelim() or curr.string == ","):
                out.append(SemType.parse(curr))
            
        if len(out) == 1: out = out[0]
        return TupleVal(out)

def τ(item):
    return SemType.type(item)

def isfun(item):
    return isinstance(SemType.type(item), tuple)
    
    
class Rule(object):
    def __init__(self, name, pattern, output):
        self.name    = str(name)
        self.pattern = φ(pattern)

        if isinstance(output, str):
            #print("Parsing", output, "will return", Span(output).debugstr())
            output = Span(output)
            if output.printlen() == 1:
                output = output[0].value()
        
        self.output = output
        #print(f"Rule output is {output}::{type(output)}")
        Rule.register(self)
    
    def run(self,target,**kwargs):
        def mylog(s): log(s,"Rule.run")
        DEBUGGING = mylog("ENTER Rule.run")

        bindings = self.pattern.match(target)
        if bindings is None: return None
        # REDO with dictstr: ??
        #DEBUGGING and mylog(f"Running Rule {self.name} with Bindings: {bindings}")#; time.sleep(1)
        
        if isinstance(bindings, list):
            DEBUGGING and mylog(f"Rule {self} received a list of binding (lists)")
            out = [self.output.update(bs) for bs in bindings]
            #out = out[0] if len(out) == 1 else out
            return out if out else None
                    
        DEBUGGING and mylog(f"Running Sem Rule {self} on {target}, Bindings:") 
        for k in bindings: DEBUGGING and mylog(f"{k} : {bindings[k]}") #refactor with dictstr?
        
        bindings.update(kwargs) #add the parameters to the bindings
        out = self.output.update(bindings)
        #print(f"Out pre-φ is {out}::{type(out)}")
        #out = φ(out) #ensure it's a phival
        #print(f"Out pre-eval is {out}::{type(out)}")
        try:
            if not hasattr(out, "ev_n"):
                out = Span.parse(str(out))
            out = out.ev_n(print_errors = False, throw_errors=True)
            if isinstance(out,Span): out = SpanVal(out)
        #except AttributeError: pass
        except: return None
                
        DEBUGGING and mylog(f"{self.name} -> {out}::{type(out)}")
        return out
    
    def register(self):
        global memo
        memo = {} # Reset memoization with new rule
        print(f"Rule {self.name} added to global rule dictionary 'rules'")
        rules[self.name] = self
    
    def deregister(name=None):
        if not name: print("Deleting all rules"); rules.clear()
        elif name in rules: print("Deleting " + name); del rules[name]
        else: print("Could not find rule " + name)
        
    def __repr__(self):
        return self.name + ": " + str(self.pattern) + " -> " + str(self.output)

        
def map(f, i):
    if isinstance(i, list) or isinstance(i, tuple):
        return tuple(builtins.map(f,i))
    if isinstance(i, set) or isinstance(i, frozenset):
        return frozenset(builtins.map(f,i))
    return builtins.map(f,i)

def filter(f, i):
    if isinstance(i, list) or isinstance(i, tuple):
        return tuple(builtins.filter(f,i))
    if isinstance(i, set) or isinstance(i, frozenset):
        return frozenset(builtins.filter(f,i))
    return builtins.filter(f,i)
        
def safe_update(d1, d2):
    if d1 is None or d2 is None: return False
    for k in d2:
        if k in d1 and d1[k] != d2[k]: return False
    d1.update(d2)
    return True

def matches(pattern, target, variables):
    if not pattern: return [{}] if not target else [] # empties match with no vars
    
    head = pattern[0]
    if ConstantVal(head).is_variable(variables): # found a variable
        # substitute each prefix of target for var and recurse
        return [{head:target[0:i], **ms} for i in range(len(target)+1)
                   for ms in matches(pattern[1:], target[i:], variables) 
                       if head not in ms or ms[head]==target[0:i] #ensure same value
               ]
    
    if not target: return [] # no match    
    if head == target[0]: # heads match
        return matches(pattern[1:], target[1:], variables) # check tails
    
    return []

def ip_parse(s, mode="eval"):
    s = ip.transform_cell(s)
    tree = ast.parse(s, mode=mode)
    tree = ip.transform_ast(tree)
    return tree

def eval_n(s, last=None):
    if s==last: return s # Base case 1: self-evaluating expression
    try: return eval_n(ip_eval(s), s)
    except: return s     # Base case 2: non-evaluating expression

#Can't remember why I returned the converted string instead of the original. 
def ip_eval(s):
    try:
        code =  f"try: _out = {s}\n"\
                f'except: _out = None' # = """{s}"""'
        ip.run_cell(code, silent=True)
        out = ip.ev("_out")
        #print("Evaluating code: |" + code + "|\n yields " + str(out) + " of type " + str(type(out)))
        return out if out != None else s
    except Error as e: 
        print("Exception in ip_eval" + str(e))
        return None
    
def istrue(b,trues={1,True}):
    """Returns true if b has implemented bool, but only for 1 or True"""
    bool(b) # Raises an error for Span or SemLiteral
    return b in trues

def noerr(f,*x,**k):
    """Converts exceptions to False, except NotImplemented"""
    try: return istrue(f(*x, **k))
    except NotImplementedError as e: raise e # Spans and SemLiterals
    #except ValueError as e: raise e # Domain Errors TODO: CHECK THIS IS OUT WITH HW4?
    except: return False

def ext(f,domain=map(ConstantVal,SemType.D["e"]),memoize=True):
    if memoize:
        hash = f"PHIEXTHASH#{f}#{domain}"
        if hash in memo: return memo[hash]

    try:
        # False and error inputs are excluded from the extension
        out = SetVal([x for x in domain if noerr(f,x)])
        if memoize: memo[hash] = out
        return out
    except Exception as e:
        #raise e
        from .semval import SemLiteral
        return SemLiteral(f"ext({f})")
    
def ι(f, domain=None):
    try:
        return max(ext(f,domain) if domain else ext(f))
    except: pass
    
    try:
        extn = [x for (x,y) in f if istrue(y)]
        return max(extn)
    except: pass
    if not isinstance(f,str):
        try: return max(f)
        except: pass
    
    from .semval import SemLiteral
    out = SemLiteral(f"ι({f})")

    # Doesn't work, since it isn't parseable yet:
    # if isinstance(f, LambdaVal):
    #     out = SemLiteral(f"[ι{f.args[0]}.{f.body}]")    
    
    out.stype = ConstantVal("e")
    return out

class ArbSet():
    def __init__(self,f,s):
        self.f = f
        self.s = s
        
    def __contains__(self,x):
        return self.f(x)
    
    def __repr__(self):
        return self.s
        
# TODO: memoize so we can memoize its __contains__ above    
def dom(f):
    def test(x):
        try:
            if τ(x) != τ(f.args[0]):
                return False
            if f.guard is not None and len(f.guard) > 0:
                f(x)
        except: return False
        return True
    
    return ArbSet(test, f"{{x | x∈{τ(f.args[0])}" + 
                      (f" & {f.guard}}}" if f.guard is not None else "}"))
