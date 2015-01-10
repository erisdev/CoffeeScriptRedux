fs = try require 'fs'
vm = try require 'vm'
escodegen = require 'escodegen'
{SourceMapConsumer} = require 'source-map'

{Compiler} = require './compiler'
{union} = require './functional-helpers'
{envEnrichments} = require './helpers'
nodeTypes = require './nodes'

exports = module?.exports ? this

hideFromStackTrace = (func) ->
  func.hideFromStackTrace = yes
  func

terminateStackTrace = (func) ->
  func.terminateStackTrace = yes
  func

evalAsFile = hideFromStackTrace do ->
  if vm?
    (code, filename) -> vm.runInThisContext "(#{code})", filename
  else do ->
    # calling eval from an alias executes in the global context
    eval_ = eval
  
    (code, filename) ->
      eval_ "(#{code})\n//@ sourceURL=#{filename}"

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

unwrap = (node) ->
  if node.body?
    unwrap node.body
  else if node.statements?.length is 1
    unwrap node.statements[0]
  else node

transform = hideFromStackTrace do ->
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

walk = hideFromStackTrace (node, visit) ->
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
    macro: (node) ->
      bindMacro = (node, name) =>
        @getFunc(node, name, macro:@helpers, cs:nodeTypes)
      
      if node instanceof nodeTypes.Function
        throw new Error('macro expects a closure with no parameters') if node.parameters.length
        @callMacro bindMacro(node), []
      else if (name = getCalleeName(node))?
        throw new Error("macro expects a closure after identifier") unless node.arguments.length is 1 and node.arguments[0] instanceof nodeTypes.Function
        @macros[name] = bindMacro(node.arguments[0], name)
        no
      else
        throw new Error("macro expects a closure or identifier")

    'macro.quote': (func) ->
      if func not instanceof nodeTypes.Function or func.parameters.length
        throw new Error('macro.codeToNode expects a closure with no parameters')
      @context.__codeNodes.push func.body
      @helpers.parse "@__codeNodes[#{@context.__codeNodes.length - 1}]"

  # included in the namespace of all macros as 'macro'
  builtinHelpers:
    require: require
    nodeToId: nodeToId
    transform: transform
    unwrap: unwrap
    walk: walk

    eval: (node, context, bindings) ->
      @execNode(node, context, bindings) if node?

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
                @helpers.uneval(item) for item in obj
              )
            else
              new nodeTypes.ObjectInitialiser(
                for key, value of obj
                  continue unless node = @helpers.uneval(value)
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
      @helpers.parse code, filename

    backquote: (values, ast) ->
      transform ast, (node) =>
        if (name = @helpers.nodeToId(node)) and values.hasOwnProperty(name)
          @helpers.uneval(values[name])
        else yes

    define: (name, func) ->
      @defineMacro name, func
    
    call: (name, args...) ->
      @callMacro name, args

  constructor: ->
    bind = (func) =>
      bound = func.bind(this)
      # for debugging purposes
      bound.toString = => "// (bound to MacroExpander)\n#{func}"
      bound
      
    @macros = {}
    @defineMacro(k, bind v) for k, v of @builtinMacros
    
    @helpers = {}
    @helpers[k] = bind(v) for k, v of @builtinHelpers
    
    @filenameStack = []
    @filename = '<internal>'
    
    @sourceMaps = {}
    
    @context =
      __macros:@macros
      __codeNodes:[]

  defineMacro: (name, fn) ->
    @macros[name] = fn
    fn.displayName ?= "<macro #{name}>"
    fn

  callMacro: (name, args) ->
    if typeof name is 'function'
      func = name
    else if name of @macros
      func = @macros[name]
    else
      throw new Error("undefined macro: #{name}")
    
    func.apply @context, args

  pushFile: (newFile = '<unknown>') ->
    @filenameStack.push @filename
    @filename = newFile
  
  popFile: ->
    @filename = @filenameStack.pop()
  
  nextId = 0
  getFunc: (node, name = "<anonymous macro #{nextId++}>", bindings) ->
    params = []
    args = []
  
    if bindings?
      for k, v of bindings
        params.push new nodeTypes.Identifier(k)
        args.push v
  
    csAst = new nodeTypes.Function(params, node)
    jsAST = Compiler.compile(csAst, bare:yes).toBasicObject()
    {map, code} = escodegen.generate jsAST,
      sourceMapWithCode: yes
      sourceMap: @filename
    
    if map = map?.toJSON()
      sourceMapId = "#{@filename}\##{name}"
      @sourceMaps[sourceMapId] = map
    
    func = evalAsFile(code, sourceMapId).apply(null, args)
    func.displayName = "<macro #{name}>"
    func

  execNode: (node, context = @context, bindings) ->
    funcNode = new nodeTypes.Function([], node)
    @getFunc(funcNode, null, bindings).call context
  
  prepareStackTrace: (error, stack) ->
    [
      "#{error.name}: #{error.message}"
      (
        for frame in stack
          func = frame.getFunction()
          name = func.displayName ? frame.getFunctionName() ? '<anonymous>'
          filename = frame.getFileName()
          
          break if func.terminateStackTrace
          continue if func.hideFromStackTrace
          
          if filename of @sourceMaps
            map = new SourceMapConsumer(@sourceMaps[filename])
            {line, column} = map.originalPositionFor
              line: frame.getLineNumber()
              column: frame.getColumnNumber()
            location = [map.sources[0], line, column]
          else
            location = [filename ? '<unknown>']
        
          "    #{name} (#{location.join ':'})"
      )...
    ].join('\n') + '\n'
  
  
  loadMacroDefinitions: (ast) ->
    walk ast, (node) =>
      if getCalleeName(node) is 'macro'
        args = (@expand arg for arg in node.arguments)
        @callMacro 'macro', args
    this

  expand: (ast, options) ->
    unless options.fullStackTrace
      _prepareStackTrace = Error.prepareStackTrace
      Error.prepareStackTrace = @prepareStackTrace.bind(this)
    
    @pushFile options.inputSource
    try
      ast = transform ast, terminateStackTrace (node) =>
        if (name = getCalleeName(node))? and @macros.hasOwnProperty(name)
          @callMacro name, node.arguments
        else
          yes
    finally
      @popFile()
      Error.prepareStackTrace = _prepareStackTrace if _prepareStackTrace?
    ast
  
  hideFromStackTrace(v) for own k, v of @prototype when typeof v is 'function'