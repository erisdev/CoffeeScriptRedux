// Generated by CoffeeScript 2.0.0-beta3
var runScripts;
window.CoffeeScript = require('./module');
CoffeeScript['eval'] = function (code, options) {
  if (null == options)
    options = {};
  if (null != options.bare)
    options.bare;
  else
    options.bare = true;
  if (null != options.optimise)
    options.optimise;
  else
    options.optimise = true;
  return eval(CoffeeScript.cs2js(code, options));
};
CoffeeScript.run = function (code, options) {
  if (null == options)
    options = {};
  options.bare = true;
  if (null != options.optimise)
    options.optimise;
  else
    options.optimise = true;
  return Function(CoffeeScript.cs2js(code, options))();
};
CoffeeScript.load = function (url, callback) {
  var xhr;
  xhr = window.ActiveXObject ? new window.ActiveXObject('Microsoft.XMLHTTP') : new XMLHttpRequest;
  xhr.open('GET', url, true);
  if ('overrideMimeType' in xhr)
    xhr.overrideMimeType('text/plain');
  xhr.onreadystatechange = function () {
    if (!(xhr.readyState === xhr.DONE))
      return;
    if (xhr.status === 0 || xhr.status === 200) {
      CoffeeScript.run(xhr.responseText);
    } else {
      throw new Error('Could not load ' + url);
    }
    if (callback)
      return callback();
  };
  return xhr.send(null);
};
runScripts = function () {
  var coffees, execute, index, scripts;
  scripts = document.getElementsByTagName('script');
  coffees = function (accum$) {
    var s;
    for (var i$ = 0, length$ = scripts.length; i$ < length$; ++i$) {
      s = scripts[i$];
      if (!(s.type === 'text/coffeescript'))
        continue;
      accum$.push(s);
    }
    return accum$;
  }.call(this, []);
  index = 0;
  (execute = function () {
    var script;
    if (!(script = coffees[index++]))
      return;
    if (script.src) {
      return CoffeeScript.load(script.src, execute);
    } else {
      CoffeeScript.run(script.innerHTML);
      return execute();
    }
  })();
  return null;
};
if ('undefined' !== typeof addEventListener && null != addEventListener) {
  addEventListener('DOMContentLoaded', runScripts, false);
} else if ('undefined' !== typeof attachEvent && null != attachEvent) {
  attachEvent('onload', runScripts);
}