jsonEq = (a,b) -> eq JSON.stringify(a), JSON.stringify(b)

suite 'Compile Time Macros', ->
  test "macro value conversion", ->
    macro TO_ARRAY (expr) -> macro.uneval [macro.eval(expr)]
    jsonEq [1], TO_ARRAY 1
    jsonEq [{a:2}], TO_ARRAY {a:2}
    jsonEq [[{c:[3,4]}]], TO_ARRAY [{c:[3,4]}]
    jsonEq [null], TO_ARRAY ->

  test "macro toId", ->
    macro STRINGIFY (a) -> macro.uneval macro.nodeToId a
    eq "test", STRINGIFY test
    eq undefined, STRINGIFY test.lala
    eq undefined, STRINGIFY test[123]
    eq undefined, STRINGIFY a3 + 4
    eq undefined, STRINGIFY 123
    eq undefined, STRINGIFY {}
    eq undefined, STRINGIFY ->

  test "macro in switch", ->
    jsonEq [1], switch STRINGIFY x
      when "x"
        TO_ARRAY 1
      when STRINGIFY z
        2

  test "macro ast construction", ->
    macro -> @i18nDict = waterBottles: "%1 bottle[s] of water"
    injectAndPluralize = (msg,arg) -> msg.replace("%1",arg).replace(/[\[\]]/g,'') # stub

    macro I18N (args...) ->
      text = macro.nodeToId args[0]
      text = @i18nDict[text] || text
      args[0] = macro.uneval text
      new cs.FunctionApplication(new cs.Identifier("injectAndPluralize"), args)

    eq "17 bottles of water", I18N(waterBottles, 17)

  test "macro cs expansion", ->
    tst = (a,b) -> a*b
    eq 144, macro -> macro.quote ->
      x = (a) -> tst(a,6) * 3
      x(5) + x(3)

  test "macro subst", ->
    macro SWAP (a,b) -> macro.backquote {x:a,y:b}, macro.quote -> [x,y] = [y,x]

    [c,d] = [1,2]
    SWAP c, d
    jsonEq [2,1], [c,d]

    tst = (a,b) -> a*b
    tst2 = -> 4
    macro CALC (c1,c2,c3,c4) ->
      func = macro.backquote {c1,c2,c3,c4}, macro.quote ->
        x = (a) -> tst(a,c1) * c2
        x(c3) + x(c4)
    eq 144, CALC 6, 3, 5, 3
    eq 96, CALC 6, 2, 5, 3
    eq -70, CALC (macro -> macro.quote -> tst2()+3), -1, 6, 4

    a = "12345"
    macro LEN (x) -> macro.backquote {x}, macro.quote(-> x.length)
    eq a.length, LEN a
    macro THIRD (x) -> macro.backquote {x}, macro.quote(-> x[3])
    eq "4", THIRD a
    macro IDX (x) -> macro.backquote {x}, macro.quote(-> {12345:321}[x])
    eq 321, IDX a

  test "subst of parameters", ->
    macro substXY (f) -> macro.backquote x:macro.quote(-> y), f
    func = substXY (x) -> x + y
    eq 6, func(3)

  test "subst of loop index", ->
    macro ->
      node = macro.backquote a:macro.parse('b'), macro.quote ->
        for a in [123..124]
          eq 123, 123
    eq 124, b

  test "macro contexts", ->
    macro -> @a = 42
    eq 42, macro -> macro.uneval @a
    # FIXME context stuff
    # macro INCR (arg) -> macro.uneval macro.eval(arg)+1
    # eq 43, INCR @a

  test "macro call within macro arguments", ->
    macro R1 (arg) -> macro.uneval(macro.eval(arg)+10)
    macro R2 (arg) -> macro.uneval(macro.eval(arg)+1)
    eq 16, R1 R2 5

  test "macro macro.quote", ->
    macro toLongBody (a,b) ->
      macro.backquote {a, b}, macro.quote ->
        test = a+b
        test = test+test
    toLongBody(3+5,4)
    eq test, 24

  test "macro hasOwnProperty safety", ->
    toString = -> 746
    eq 746, toString()

  test "macro subst hasOwnProperty safety", ->
    eq "12", macro -> macro.backquote a:macro.parse('b'), macro.parse('12.toString()')

  test "macro code block insert", ->
    eq 12*13*14, macro ->
      macro.backquote code:macro.parse("x++\ny = 13\nz = 14"), macro.quote ->
        x = 11
        code
        x  * y * z

  test "macro subst with reserved names as properties", ->
    y = void: {case: 7}
    eq 7, macro ->
      macro.backquote x:macro.parse("y.void"), macro.quote(-> x.case)

  test "macro subst should not substitute property access", ->
    a = {b: 2, c: 3}
    eq 2, macro -> macro.backquote b:macro.parse('c'), macro.quote(-> a.b)
    return
