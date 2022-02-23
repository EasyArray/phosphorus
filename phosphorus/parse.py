from tokenize import tokenize, untokenize, TokenInfo, TokenError
from token import *
from io import BytesIO
import time

class Token():
    def __init__(self, typ, string, spacebefore=""):
        #print(f"Value {string}::{type(string)}")
        self.string = str(string)
        self.type = typ
        self.spacebefore = spacebefore
        
    def __str__(self): return self.spacebefore + self.string
    def __repr__(self): return self.string
    
    def debugstr(self): return f"{self.string}::{tok_name[self.type]} (spaces:{self.spacebefore})"

    def value(self):
        #TODO: fix these imports
        from .phival import φ, NumVal
        import ast
        if self.type == NUMBER: return NumVal(self.string)
        if self.type == STRING: return φ(ast.literal_eval(self.string))
        return φ(self.string)
    
    def fromTokenInfo(curr,prevend=(1,0)):
        if curr.start[0] > prevend[0]:
            prevend = (curr.start[0],0)
        diff = curr.start[1] - prevend[1]
        diff = diff if diff>0 else 0
        #print(curr.string + "::" + tok_name[curr.type] + f"({curr.type})")
        #print("currstart", curr.start[1], "prevend", prevend)
        return Token(curr.type, curr.string, " "*diff)
    
    delims = {"{":"}", "(":")", "[":"]", "⟨":"⟩"}
    def isopendelim(self):
        return self.string in Token.delims
    def isdelim(self):
        return self.isopendelim() or self.string in Token.delims.values()
    def matches(self,delim):
        return delim in Token.delims and self.string == Token.delims[delim]
    def isvariable(self):
        return self.type == NAME


class Span(list):    
    def __init__(self, s=""):
        self.type = None
        self.spaceafter = ""
        super().__init__([])
        if s: Span.parse(s, None, self)
        
    def __repr__(self):
        out = "".join(str(tok) for tok in self.leaves())
        return out + self.spaceafter #"❰" + out + "❱"        
            
    def value(self):
        return self
    
    def semtype(self):
        from .phival import ConstantVal
        return ConstantVal("t")
    
    def __bool__(self): raise NotImplementedError
    
    @property
    def string(self): return str(self)
        
    @property
    def spacebefore(self): return self[0].spacebefore
    
    @spacebefore.setter
    def spacebefore(self,s): self[0].spacebefore = s
    
    def leaves(self):
        for i in self:
            if isinstance(i,Span): yield from i.leaves()
            else:                  yield i
                
    def isdelim(self): return False
    
    def debugstr(self):
        return str(self) + "::" + (self.type if self.type else "No type") + " = " + "".join([t.debugstr() for t in self])
    
    def printlen(self):
        return len([o for o in self if o.string])
        
    #Idea: instead of just the lambdas, eval each Span as possible?
    def update(self,subs):
        def mylog(s): log(s,"Span.update")
        from .phival import LambdaVal, ConstantVal
        
        mylog(f"Updating {self.debugstr()} with subs {subs}")
        
        span = Span()
        span.type = self.type
        enum = enumerate(self)
        for n,item in enum:
            peek = None
            if len(self) > n+1:
                peek = self[n+1]
            
            mylog(f"Checking {item.debugstr()} in subs? {item.string in subs}")
            if item.type == NAME and item.string in subs and (peek.string != "=" if peek is not None else True):
                s = item.string
                spaces = item.spacebefore
                #item = ConstantVal(s).update(subs)                
                item = subs[item.string]
                mylog(f"Replacing {s} -> {item}::{type(item)}")
                if not isinstance(item, LambdaVal):
                    #s = get_ipython().transform_cell(str(item)).strip() #remove final newline
                    s = str(item) #Problem if we want to use keywords as ConstantVals?
                    mylog(f"|{item}| transforms to |{s}|")
                    item = Span.parse(spaces + s)
                    mylog(f"Parsed: |{item}|")
                    if item.printlen() == 1: item = item[0]
            
            if item.type == "lambda":
                mylog("Found lambda span " + str(item))
                item = LambdaVal.parse(item)
                mylog("Parsed " + str(item))
                if subs: item = item(**subs)
                mylog("With subs " + str(item))
                
            if isinstance(item, LambdaVal):
                mylog("Found lambda " + str(item))
                if peek is not None:
                    mylog(f"Next item: {peek}::{type(peek)}")
                    if isinstance(peek, Span) and peek[0].string == "(":
                        peek = peek.update(subs) #apply bindings to args of lambda
                        item = item.sub({item.args[0] : peek.ev(False, False)}) #Basically run the func without checking types/domain restrictions
                        next(enum) #skip the arg

                mylog("Finally" + str(item))
                item = Span.parse(str(item))
                #span.append(item)
                #item = Span.parse("(" + ",".join(f"{key}={value}" for key,value in subs.items()) + ")")[0]
                mylog("Adding " + str(item) + " to lambda")

            elif isinstance(item,Span):
                item = item.update(subs) #Could this do too many replacements?
            
            span.append(item)
        mylog("Returning" + item.debugstr())
        return span

#NOTE: Can't for the life of me get the async runcode to work...

#     def ev(self):
#         from Phosphorus import replace_elements, ValWrapper
#         import ast; import asyncio
#         ip = get_ipython()
#         s = replace_elements(str(self))
#         s = f"try: _out = {s}\n"\
#             f'except Exception as e: _out = e'
#         tree = ast.parse(s, mode="exec")
#         tree = ast.fix_missing_locations(ValWrapper().visit(tree))
#         code = compile(tree, "Phosphorus Code", mode="exec")
#         loop = asyncio.get_running_loop()
#         tsk = loop.create_task(ip.run_code(code))
#         while not tsk.done(): pass
#         #ip.run_cell("_out = " + str(self), silent=True)
#         out = ip.ev("_out")
#         if isinstance(out, Exception):
#             print("Error in Phosphorus code: ", out)
#             return self
#         return out

    def ev(self, print_errors = True, throw_errors = False):
        ip = get_ipython()
        s = f"try: _out = {self}\n"\
            f'except Exception as e: _out = e'
        #print("Evaluating string", s, "in", self.debugstr())
        
        ip.run_cell(s, silent=True)
        out = ip.ev("_out")
        #print(f"Got {out}::{type(out)}; =self:{out==self}")
        
        if isinstance(out, Exception):
            if print_errors: printerr(out, f"in Phosphorus code |{self}|")
            if throw_errors: raise out
            return self
        return out
    
    def ev_n(self, count=100, print_errors = True, throw_errors = False):
        #print(f"Eval {self} count {count}" )
        try:
            out = self.ev(print_errors = print_errors, throw_errors = throw_errors)
            if not isinstance(out, Span): # Base case 1: got an actual value
                return out
            if out == self: return self   # Base case 2: self-evaluating expression
            if not count:                 # Base case 3: infinite loop
                print(f"Looped too many times in evaluating {self}")
                return self
            # Recursive step
            return out.ev_n(count-1, throw_errors = throw_errors)
        except Exception as e:
            if print_errors: printerr(e, f"in evaluation loop for {self}")
            if throw_errors: raise e
            return self     # Base case 3: Unexpected exception
        
    ignores = {INDENT, ENDMARKER, DEDENT, ENCODING}
    def parse(g,delim=None,span=None,subs={}):
        def mylog(s): log(s,"Span.parse")
        if span is None: span = Span()
        def cleanup(g):
            """ Ignores non-printing tokens, but fixes spacing issues and 
                substitutes for our "escape" characters """
            spaces = ""
            for t in g:
                if t.type in Span.ignores or not t.string:
                    spaces += t.spacebefore
                    if t.type == INDENT: spaces += t.string
                    continue
                
                if t.type == ERRORTOKEN and t.string.isspace():
                    spaces += t.spacebefore + t.string
                    continue
                    
                if span.type != "lambda" and t.string in subs:
                    #print("Found in subs:", t.debugstr())
                    g.send(subs[t.string]) #ignore token returned here, will be sent again
                    continue
                    
                if spaces:
                    t.spacebefore += spaces
                    spaces = ""
                    
                if t.string and t.string[0] == "λ":
                    t.type = OP
                    if len(t.string) > 1:
                        rest = t.string[1:]
                        t.string = "λ"
                        yield t
                        t = Token(NAME, rest)
                        
                yield t
            
        if isinstance(g, str):
            #print("Parsing " + g )
            #g = tokenize(BytesIO(g.encode('utf-8')).readline)
            g = totokens(g)

        if delim:
            span.append(delim)
            delim = delim.string
            
        for tok in cleanup(g): #totokens(g):
            mylog(f"Found token {tok.debugstr() if tok else 'NONE'}")
                
            if not tok.isdelim():
                if len(span) and span[-1].isdelim() and tok.string == 'λ':# or tok.string == "lambda":
                    mylog("Inside lambda Span")
                    span.type = "lambda"
                    #subs = {}
                span.append(tok)

            elif delim and tok.matches(delim):
                mylog("Close delim " + tok.string)
                span.append(tok) #check for NEWLINE??
                break

            elif tok.isopendelim():
                mylog("Open delim " + tok.string)
                if len(span)>0 and span[-1].string == 'λ':
                    mylog("Canceling lambda Span, explicit fn")
                    span.type = ""
                subspan = Span.parse(g,tok,subs={} if span.type == "lambda" else subs)
                span.append(subspan)

            else: raise SyntaxError(f"Unmatched delimiter: {tok.debugstr()}")

            first = False
        
        mylog(f"Parsed {span} {span.debugstr()}")
        return span
    
def totokens(s):
    """ Returns our internal Token class instead of TokenInfos. Calculates spaces
        before each token. Also accepts "send" requests, which send a replacement for
        the previous token, then picks up where we were. """
    # Raw TokenInfo generator
    g = tokenize(BytesIO(s.encode('utf-8')).readline)
    # Set previous location to beginning
    prevend=(1,0)
    for tokeninfo in g:
        #print("Raw Token:", tokeninfo, "Prev End", prevend)
        token = Token.fromTokenInfo(tokeninfo, prevend)
        repl = yield token
        if repl is not None: #Got a replacement for the previous token
            #print("Found replacement", repl)
            yield # We don't check the return value for the send call
            try: yield from totokens(repl)
            except TokenError as e: pass #Ignore unclosed delimiters
        prevend = tokeninfo.end
    
_debugging_contexts = dict()
def debugging(context="", on = True):
    global _debugging_contexts
    old =_debugging_contexts.get(context)
    _debugging_contexts[context] = on
    return old
    
def log(s,context=""):
    if _debugging_contexts.get("") or _debugging_contexts.get(context):
        print(s)
        
_errors_on = True
def errors_on(b, context=""):
    global _errors_on
    old = _errors_on
    _errors_on = b
    #print("Set Errors " + str(b))
    return old

import traceback
def printerr(e, s=""):
    if not _errors_on: 
        #print("Errors Off")
        return
    print(type(e).__name__, s, ":", e)
    #traceback.print_exc()
