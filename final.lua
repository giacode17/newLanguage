
local lpeg = require "lpeg"
local pt = require "pt"
local C, Ct, P, R, S, V = lpeg.C, lpeg.Ct, lpeg.P, lpeg.R, lpeg.S, lpeg.V

----------------------------------------------------
local function I (msg) --l4:To show debugging msg
  return P(function () print(msg); return true end)
end

--[[||Parser : using metaprogramming
local function node (tag, ...)
  local labels = table.pack(...)
  local params = table.concat(labels, ", ")
  local fields = string.gsub(params, "(%w+)", "%1 = %1")
  local code = string.format(
    "return function (%s) return {tag = '%s', %s} end",
    params, tag, fields)
  return assert(load(code))()
end
--]]



-- Without using meta programming
local function node(tag, ...)
	local labels = table.pack(...)

	return function(...)
		local params = table.pack(...)
		local result = { tag = tag }

		for i = 1, #labels do
			result[labels[i]] = params[i]
		end

		return result
  end
end

--
local function nodeSeq (st1, st2)
  if st2 == nil then
    return st1
  else
    return {tag = "seq", st1 = st1, st2 = st2}
  end
end

local function nodeExp(e1, op, e2)
  if op == nil then
    return e1
  else
    return { tag = "binop", e1 = e1, op = op, e2 = e2 }
  end
end
--|| Tokens
local alpha = R("AZ", "az")
local underscore = S("_") --jh
local digit = R("09")
local float = C(digit^0 * P(".") * digit^1) --jh
local hex = C("0" * S("x,X") * digit^1 * R("af")^1 * R("AF")^1) --jh
local alphanum = alpha + digit + underscore --jh

local comment = "#" * (P(1) - "\n")^0 -- l4 :any character except the new line
local maxmatch = 0  --l4 for the time capture

local space = V"space"
local unary = S("+-")^-1 --jh
local numeral = ( unary * ( hex + float + (digit^1)) ) / tonumber / node("number", "val")  * space--jh

local reserved = {"@", "return", "if", "else", "while", "new", "function", "var"}
local excluded = P(false)
for i = 1, #reserved do
  excluded = excluded + reserved[i]
end
excluded = excluded * -alphanum

local ID = V"ID" --l7: def of ID move to inside of Grammar   
local var = ID / node("variable", "var")

--l4: to control space following codetoken such as ret, semicolon...
local function T (t)
  return t * space
end

--l4: func for reserve words.
local function Rw (t)
  assert(excluded:match(t)) --check for excluded reserve words.
  return t * -alphanum * space
end

--||Operator
local opA = C(S"+-") * space
local opM = C(S"*/%") * space --jh  %,*,/ same priority
local opE = C(S"^") * space --jh the highst priority
local opC = C((S"<>")* P("=")^-1 + "==" +"!=") * space --jh
local opL = C(P("and") + P("or")) * space --jh
local opN = P("!") * space --jh



-- Convert a list {n1, "+", n2, "+", n3, ...} into a tree
-- {...{ op = "+", e1 = {op = "+", e1 = n1, n2 = n2}, e2 = n3}...}
local function foldBin (lst)  --For the Binary opr tree
  local tree = lst[1]
  for i = 2, #lst, 2 do
    tree = { tag = "binop", e1 = tree, op = lst[i], e2 = lst[i + 1] }
  end
  return tree
end

local function foldLogical(lst)
  local tree = lst[1]
  for i = 2, #lst, 2 do
    tree = { tag = "logicalop", e1 = tree, op = lst[i], e2 = lst[i + 1] }
  end
  return tree
end

local function foldIndex (lst) --lhs list
  local tree = lst[1]
  for i = 2, #lst do
    tree = { tag = "indexed", array = tree, index = lst[i] }
  end
  return tree
end

--||Variable for grammar
local lhs = V"lhs"
local call = V"call"
local factor = V"factor"
local term1 = V"term1"
local term2 = V"term2"
local term3 = V"term3"
local exp = V"exp"
local stat = V"stat"
local stats = V"stats"
local block = V"block"
local funcDec = V"funcDec" --function declaration
local args = V"args"
local params = V"params"

--||Table for Grammar 
grammar = P{"prog",
  --l7: multiple (1 more) function declaration make Ct
  prog = space * Ct(funcDec^1) * -1, 

  funcDec = Rw"function" * ID * T"(" * params * T")" * block
              / node("function", "name", "params", "body"),--l7: put the inside node 

  params = Ct((ID * (T"," * ID)^0)^-1),--^-1: optional
  
  stats = stat * (T";" * stats)^-1 / nodeSeq,

  block = T"{" * stats * T";"^-1 * T"}" / node("block", "body"),

  stat = block
      --l8: var: local valriable name = init val of local var./put node: local, name,init
       + Rw"var" * ID * T"=" * exp / node("local", "name", "init") 
       + Rw"if" * exp * block * (Rw"else" * block)^-1
           / node("if1", "cond", "th", "el")
       + Rw"while" * exp * block / node("while1", "cond", "body")
       + call --l7: funcion call
       + lhs * T"=" * exp / node("assgn", "lhs", "exp")
       + Rw"return" * exp / node("ret", "exp")
       + Rw"@" * exp / node("ptst", "exp"),

  lhs = Ct(var * (T"[" * exp * T"]")^0) / foldIndex,

  call = ID * T"(" * args * T")" / node("call", "fname", "args"), --for args

  args = Ct((exp * (T"," * exp)^0)^-1),

  factor = Rw"new" * T"[" * exp * T"]" / node("new", "size")
         + numeral
         + T"(" * exp * T")"
         + call 
         + lhs,
  exp = term3,
  term3 = Ct(term2 * (opA * term2)^0) / foldBin,
  term2 = Ct(term1 * (opM * term1)^0) / foldBin, --jh
  term1 = Ct(factor * (opE * factor)^0) / foldBin, --jh
  space = (S(" \t\n") + comment)^0
            * P(function (_,p)
                  maxmatch = math.max(maxmatch, p);
                  return true
                end),
  ID = (C(alpha * alphanum^0) - excluded) * space
     
}


local function syntaxError (input, max)
  io.stderr:write("syntax error\n")
  io.stderr:write(string.sub(input, max - 10, max - 1),
        "|", string.sub(input, max, max + 11), "\n")
end

--||Parser
local function parse (input)
  local res = grammar:match(input)
  if (not res) then
    syntaxError(input, maxmatch)
    os.exit(1)
  end
  return res
end

--Compiler------------------------------------------
local Compiler = { funcs = {}, vars = {}, nvars = 0, locals = {} }
--l7: sequnce of code ->funcs : to funcs operate indivisual
function Compiler:addCode (op)
  local code = self.code
  code[#code + 1] = op
end
--Operator Instruction for compiler
local ops = {["+"] = "add", ["-"] = "sub",
             ["*"] = "mul", ["/"] = "div", ["%"] = "mod", ["^"] = "expn",
             ["<"] = "les", [">"] = "grt", ["<="] = "eqles", [">="] = "eqgrt",
             ["=="] ="eql", ["!="] ="neql"}

function Compiler:var2num (id)
  local num = self.vars[id]
  if not num then
    num = self.nvars + 1
    self.nvars = num
    self.vars[id] = num
  end
  return num
end


function Compiler:currentPosition ()
  return #self.code
end

function Compiler:codeJmpB (op, label)
  self:addCode(op)
  self:addCode(label)
end

function Compiler:codeJmpF (op)
  self:addCode(op)
  self:addCode(0)
  return self:currentPosition()
end

function Compiler:fixJmp2here (jmp)
  self.code[jmp] = self:currentPosition()
end

--l8: Find loc var by name. if yes, return idx, else nil
function Compiler:findLocal (name)
  local vars = self.locals
  for i = #vars, 1, -1 do
    if name == vars[i] then
      return i
    end
  end
  local params = self.params
  for i = 1, #params do
    if name == params[i] then
      return -(#params - i)--previous params : base
    end
  end
  return false   -- not found
end

--l7: From codeExp by "call"_ check the fname is here or not
function Compiler:codeCall (ast) 
  local func = self.funcs[ast.fname]
  if not func then
    error("undefined function " .. ast.fname)
  end
  local args = ast.args --l8.After func, we check #of args
  if #args ~= #func.params then
    error("wrong number of arguments calling " .. ast.fname)
  end
  for i = 1, #args do
    self:codeExp(args[i]) --create code for each args
  end
  self:addCode("call") --if yes implement the instruction
  self:addCode(func.code) --func called recursively so set the argument which func was called 
end

function Compiler:codeExp (ast)
  if ast.tag == "number" then
    self:addCode("push")
    self:addCode(ast.val)
  elseif ast.tag == "call" then --l7.tree of codeCall
    self:codeCall(ast)
  elseif ast.tag == "variable" then
    local idx = self:findLocal(ast.var) --l8 find local var
    if idx then
      self:addCode("loadL") --var is local var
      self:addCode(idx)
    else
      self:addCode("load") --var is global var
      self:addCode(self:var2num(ast.var))
    end
  elseif ast.tag == "indexed" then
    self:codeExp(ast.array)
    self:codeExp(ast.index)
    self:addCode("getarray")
  elseif ast.tag == "new" then
    self:codeExp(ast.size)
    self:addCode("newarray")
  elseif ast.tag == "binop" then
    self:codeExp(ast.e1)
    self:codeExp(ast.e2)
    self:addCode(ops[ast.op])
  else error("invalid tree")
  end
end

function Compiler:codeAssgn (ast)
  local lhs = ast.lhs
  if lhs.tag == "variable" then
    self:codeExp(ast.exp)
    local idx = self:findLocal(lhs.var) -- name of the loc var.
    if idx then
      self:addCode("storeL") --if yes:store loc. var
      self:addCode(idx)
    else
      self:addCode("store") --else: store glob.var
      self:addCode(self:var2num(lhs.var))
    end
  elseif lhs.tag == "indexed" then
    self:codeExp(lhs.array)
    self:codeExp(lhs.index)
    self:codeExp(ast.exp)
    self:addCode("setarray")
  else error("unkown tag")
  end
end

--l7: func block, just compile body of the block
function Compiler:codeBlock (ast)
  local oldlevel = #self.locals
  self:codeStat(ast.body)
  local n = #self.locals - oldlevel   --l8: #of new local variables
  if n > 0 then
    for i = 1, n do table.remove(self.locals) end
    self:addCode("pop")
    self:addCode(n)
  end 
end

function Compiler:codeStat (ast)
  if ast.tag == "assgn" then
    self:codeAssgn(ast)
  elseif ast.tag == "local" then --l8: local
    self:codeExp(ast.init)--code of initial value
    self.locals[#self.locals + 1] = ast.name --name of local var.
  elseif ast.tag == "call" then --l7: function call
    self:codeCall(ast)
    self:addCode("pop")
    self:addCode(1) --l7: pop only 1 element(return only 1 result)
  elseif ast.tag == "block" then --l7: fuct block
    self:codeBlock(ast)
  elseif ast.tag == "seq" then
    self:codeStat(ast.st1)
    self:codeStat(ast.st2)
  elseif ast.tag == "ret" then
    self:codeExp(ast.exp)
    self:addCode("ret")
    self:addCode(#self.locals + #self.params)--l8:local var
  elseif ast.tag == "ptst" then
    self:codeExp(state, ast.exp)
    self:addCode(state, "print")
  elseif ast.tag == "while1" then
    local ilabel = self:currentPosition()
    self:codeExp(ast.cond)
    local jmp = self:codeJmpF("jmpZ")
    self:codeStat(ast.body)
    self:codeJmpB("jmp", ilabel)
    self:fixJmp2here(jmp)
  elseif ast.tag == "if1" then
    self:codeExp(ast.cond)
    local jmp = self:codeJmpF("jmpZ")
    self:codeStat(ast.th)
    if ast.el == nil then
      self:fixJmp2here(jmp)
    else
      local jmp2 = self:codeJmpF("jmp")
      self:fixJmp2here(jmp)
      self:codeStat(ast.el)
      self:fixJmp2here(jmp2)
    end
  else error("invalid tree")
  end
end

--l7: for Function code
--list of code makes to table, take body, every func return 0
function Compiler:codeFunction (ast)
  local code = {}
  self.funcs[ast.name] = {code = code, params = ast.params}
  self.code = code
  self.params = ast.params
  self:codeStat(ast.body)
  self:addCode("push")
  self:addCode(0)
  self:addCode("ret")
  self:addCode(#self.locals + #self.params)
end

--l7: check for functions called main or not
local function compile (ast)
  --compile each func's ast code
  for i = 1, #ast do
    Compiler:codeFunction(ast[i])
  end
  --find there is main or not
  local main = Compiler.funcs["main"] 
  if not main then
    error("no function 'main'")
  end
  return main.code
end

----------------------------------------------------
--Implement call opcode, mem: memory
local function run (code, mem, stack, top)
  local pc = 1 --program counter
  local base = top --loc var = base +1
  while true do
  --[[
  io.write("--> ")
  for i = 1, top do io.write(stack[i], " ") end
  io.write("\n", code[pc], "\n")
  --]]
    if code[pc] == "ret" then
      local n = code[pc + 1]    --l8: number of active local variables : we should remove on the stack
      stack[top - n] = stack[top]
      top = top - n
      return top
--l7: this run call each function recursively
--code: func code, mem: global mem, top: argus    
    elseif code[pc] == "call" then
      pc = pc + 1 --goes to the next instruction 
      local code = code[pc]
      top = run(code, mem, stack, top)
    elseif code[pc] == "pop" then
      pc = pc + 1
      top = top - code[pc]
    elseif code[pc] == "push" then
      pc = pc + 1
      top = top + 1
      stack[top] = code[pc]
    elseif code[pc] == "add" then
      stack[top - 1] = stack[top - 1] + stack[top]
      top = top - 1
    elseif code[pc] == "sub" then
      stack[top - 1] = stack[top - 1] - stack[top]
      top = top - 1
    elseif code[pc] == "mul" then
      stack[top - 1] = stack[top - 1] * stack[top]
      top = top - 1
    elseif code[pc] == "div" then
      stack[top - 1] = stack[top - 1] / stack[top]
      top = top - 1
    elseif code[pc] == "mod" then --jh
      stack[top - 1] = stack[top - 1] % stack[top]
      top = top - 1
    elseif code[pc] == "expn" then --jh
      stack[top - 1] = stack[top - 1] ^ stack[top]
      top = top - 1
    elseif code[pc] == "les" then
      stack[top - 1] = stack[top - 1] < stack[top] and 1 or 0
      top = top - 1
    elseif code[pc] == "grt" then
      stack[top - 1] = stack[top - 1] > stack[top] and 1 or 0
      top = top - 1    
    elseif code[pc] == "eqles" then
      stack[top - 1] = stack[top - 1] <= stack[top] and 1 or 0
      top = top - 1
    elseif code[pc] == "eqgrt" then
      stack[top - 1] = stack[top - 1] >= stack[top] and 1 or 0
      top = top - 1   
    elseif code[pc] == "eql" then
      stack[top - 1] = stack[top - 1] == stack[top] and 1 or 0
      top = top - 1
    elseif code[pc] == "neql" then
      stack[top - 1] = stack[top - 1] ~= stack[top] and 1 or 0
      top = top - 1
    
    elseif code[pc] == "not" then ------
      stack[top] = stack[top] == 0 and 1 or 0  

    elseif code[pc] == "loadL" then --loc var
      pc = pc + 1
      local n = code[pc]
      top = top + 1
      stack[top] = stack[base + n]
    elseif code[pc] == "storeL" then --loc var
      pc = pc + 1
      local n = code[pc]
      stack[base + n] = stack[top]
      top = top - 1
    elseif code[pc] == "load" then --global var 
      pc = pc + 1
      local id = code[pc]
      top = top + 1
      stack[top] = mem[id]
    elseif code[pc] == "store" then
      pc = pc + 1
      local id = code[pc]
      mem[id] = stack[top]
      top = top - 1
    elseif code[pc] == "print" then
      print(stack[top])
      top = top - 1
    elseif code[pc] == "newarray" then
      local size = stack[top]
      stack[top] = { size = size }
    elseif code[pc] == "getarray" then
      local array = stack[top - 1]
      local index = stack[top]
      stack[top - 1] = array[index]
      top = top - 1
    elseif code[pc] == "setarray" then
      local array = stack[top - 2]
      local index = stack[top - 1]
      local value = stack[top]
      array[index] = value
      top = top - 3
    elseif code[pc] == "jmp" then
      pc = code[pc + 1]
    elseif code[pc] == "jmpZ" then
      pc = pc + 1
      if stack[top] == 0 or stack[top] == nil then
        pc = code[pc]
      end
      top = top - 1
    else error("unknown instruction " .. code[pc])
    end
    pc = pc + 1
  end
end

local input = io.read("a")
local ast = parse(input)
print(pt.pt(ast))
local code = compile(ast)
print(pt.pt(code))
local stack = {}
local mem = {}
run(code, mem, stack, 0)
print(stack[1])