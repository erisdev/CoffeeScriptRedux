fs = require 'fs'
escodegen = require 'escodegen'

{Compiler} = require './compiler'
{union} = require './functional-helpers'
{envEnrichments} = require './helpers'
nodeTypes = require './nodes'

exports = module?.exports ? this

evalInGlobalContext = eval
getFunc = (ast) ->
  # if bindings?
  #   bindingNames = []
  #   bindingValues = []
  #   for k, v of bindings
  #     bindingNames.push k
  #     bindingValues.push v
  #   ast = new nodeTypes.Function(bindingNames, ast)
  jsAST = Compiler.compile(ast, bare:yes).toBasicObject()
  {map, code} = escodegen.generate jsAST,
    sourceMapWithCode:yes
    sourceMap: '(macro)' # TODO figure out real filename
  func = evalInGlobalContext "(#{code})"
  # func = func.apply null, bindingValues if bindings?
  func.sourceMap = map
  func

callFunc = (func, obj, args = [], useLocation, name) ->
  try
    func.apply obj, args
  catch e
    throw e if e instanceof SyntaxError
    e.srcMap = func.sourceMap
    throw e

callFunc.stopStackTrace = yes

execNode = (node, context, bindings) ->
  if bindings?
    params = []
    args = []
    for k, v of bindings
      params.push k
      args.push v
  funcNode = new nodeTypes.Function(params ? '', node)
  callFunc getFunc(funcNode), context, args

nodeToId = (node, dotted = no) ->
  if node instanceof nodeTypes.Identifier
      node.data
  else if dotted and node instanceof nodeTypes.StaticMemberAccessOps
    "#{nodeToId node.expression}.#{node.memberName}"
  # else if node instanceof nodeTypes.DynamidMemberAccessOps
  #   "#{nodeToId node.expression}.#{nodeToId node.indexingExpr}"
  else undefined

getCalleeName = (node) ->
  if node instanceof nodeTypes.FunctionApplications
    nodeToId node.function, yes

getLocation = (node) ->
  if node.line? # assume this means other location information is available
    loc =
      line: @line = node.line
      column: @column = node.column
      offset: node.offset

addMacroParameters = (node) ->
  node.parameters.unshift new nodeTypes.Identifier('cs')
  node.parameters.unshift new nodeTypes.Identifier('macro')
  node

unwrap = (node) ->
  if node.body?
    unwrap node.body
  else if node.statements?.length is 1
    unwrap node.statements[0]
  else node

transform = do ->
  _handleReturn = (node, res, nullOK) ->
    if res is yes then node
    else if res instanceof nodeTypes.Nodes then res
    else if nullOK then undefined
    else new nodeTypes.Undefined

  transform = (node, visit) ->
    node = node.clone()
    for childName in node.childNodes when node[childName]?
      if childName in node.listMembers
        node[childName] =
          for child in node[childName]
            res = child
            while res instanceof nodeTypes.Nodes
              child = transform(res, visit)
              res = visit(child)
            continue unless res is yes
            child
      else
        res = child = node[childName]
        while res instanceof nodeTypes.Nodes
          child = transform(res, visit)
          res = visit(child)
        if res is yes
          node[childName] = child
        else
          node[childName] = new nodeTypes.Undefined
    node

  # (ast, visit) ->
  #   transform ast, (node) ->
  #     console.log 'visiting', node
  #     visit node

walk = (node, visit) ->
  for childName in node.childNodes when node[childName]?
    if childName in node.listMembers
      visit walk(child, visit) for child in node[childName]
    else
      child = node[childName]
      visit walk(child, visit)
  node

class exports.MacroExpander
  @expand = (csAst, options = {}) =>
    macro = new this
    if options.macros?
      macro.defineMacro name, fn for name, fn of options.macros
    macro.expand csAst, options

  builtinMacros:
    macro: (macro, cs, node) ->
      if node instanceof cs.Function
        throw new Error('macro expects a closure with no parameters') if node.parameters.length
        callFunc getFunc(addMacroParameters node), this, [macro, cs], '(macro)'
      else if (name = getCalleeName(node))?
        throw new Error("macro expects a closure after identifier") unless node.arguments.length is 1 and node.arguments[0] instanceof cs.Function
        @__macros[name] = getFunc(addMacroParameters node.arguments[0])
        no
      else
        throw new Error("macro expects a closure or identifier")

    'macro.quote': (macro, cs, func) ->
      if func not instanceof cs.Function or func.parameters.length
        throw new Error('macro.codeToNode expects a closure with no parameters')
      @__codeNodes.push func.body
      macro.parse "@__codeNodes[#{@__codeNodes.length - 1}]"

  # included in the namespace of all macros as 'macro'
  helpers:
    require: require
    nodeToId: nodeToId
    transform: transform
    walk: walk

    eval: (node, context = @__context) ->
      execNode(node, context) if node?

    uneval: (obj) ->
      if obj instanceof nodeTypes.Nodes
        obj
      else if obj is undefined
        new nodeTypes.Undefined
      else if obj is null
        new nodeTypes.Null
      else
        switch typeof obj
          when 'boolean' then new nodeTypes.Bool(obj)
          when 'number' then new nodeTypes.Float(obj)
          when 'string' then new nodeTypes.String(obj)
          when 'object'
            if Array.isArray(obj)
              new nodeTypes.ArrayInitialiser(
                @uneval(item) for item in obj
              )
            else
              new nodeTypes.ObjectInitialiser(
                for key, value of obj
                  continue unless node = @uneval(value)
                  new nodeTypes.ObjectInitialiserMember(new nodeTypes.String(key), node)
              )
          else new nodeTypes.Undefined

    parse: do ->
      parse = null # lazy require to avoid circular dependency
      (code, inputSource = '(macro)') ->
        {parse} = require './module' unless parse?
        unwrap parse(code, {inputSource, raw:yes})

    parseFile: (filename) ->
      code = fs.readFileSync(filename, 'utf8')
      code = code.substr 1 if code.charCodeAt(0) is 0xFEFF
      @parse code, filename

    backquote: (values, ast) ->
      transform ast, (node) =>
        if (name = @nodeToId(node)) and values.hasOwnProperty(name)
          @uneval(values[name])
        else yes

  constructor: ->
    @macros = Object.create @builtinMacros
    @context =
      __macros:@macros
      __codeNodes:[]

  defineMacro: (name, fn) ->
    @macros[name] = fn

  loadMacroDefinitions: (ast) ->
    walk ast, (node) =>
      if getCalleeName(node) is 'macro'
        args = [@helpers, nodeTypes, (@expand arg for arg in node.arguments)...]
        callFunc @macros.macro, @context, args, getLocation(node), 'macro'
    this

  expand: (ast) ->
    transform ast, (node) =>
      if (name = getCalleeName(node))? and @macros.hasOwnProperty(name) or @builtinMacros.hasOwnProperty(name)
        args = [@helpers, nodeTypes, node.arguments...]
        try
          callFunc @macros[name], @context, args, getLocation(node), name
        catch e
          console.log require('util').inspect node.toBasicObject(), depth:999
          throw e
      else
        yes
