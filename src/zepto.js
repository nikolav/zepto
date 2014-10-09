//     Zepto.js
//     (c) 2010-2014 Thomas Fuchs
//     Zepto.js may be freely distributed under the MIT license.

// deps:
//   lodash.js
//   q, home-made utility set


// closure wrapper globals

var ADDEVENTLISTENER        = 'addEventListener';
var CHILDNODES              = 'childNodes';
var CHILDREN                = 'children';
var COMPAREDOCUMENTPOSITION = 'compareDocumentPosition';
var CONTAINS                = 'contains';
var DISPATCHEVENT           = 'dispatchEvent';
var REMOVEEVENTLISTENER     = 'removeEventListener';

var globals = q.globals;

var lodash    = q._;
var modernize = globals['Modernizr'] || {};

var afilter          = q.arr.filter;
var amap             = q.arr.map;
var aslice           = q.arr.slice;
var aslice_          = q.arr.slice_;
var callback_true    = q.func.fntrue;
var corbind          = q.func.corbind;
var coreach          = lodash.each;
var corindexof       = q.arr.index;
var cortrim          = lodash.trim;
var createElement    = q.dom.mkel;
var doce             = q.dem.de;
var getbody          = q.dom.body;
var getComputedProp  = q.dom.style.prop;
var pA               = q.arr._;
var paste            = q.obj.paste;
var toClassString    = q.obj.str;

var supportz = 
(function () {
  
  var s = {};
  
  s.listeners                = (true === modernize.listeners) || ((ADDEVENTLISTENER in doce) && (REMOVEEVENTLISTENER in doce) && (DISPATCHEVENT in doce));
  s[CHILDREN]                = CHILDREN in doce;
  s[COMPAREDOCUMENTPOSITION] = COMPAREDOCUMENTPOSITION in doce;
  s[CONTAINS]                = CONTAINS in doce;
  
  return s;
})();

var Zepto = (function(supportz) {
  var 
    zepto = {},
    key, $, classList,
    elementDisplay = {},
    classCache = {},
    cssNumber = {
      'column-count': 1,
      'columns'     : 1,
      'font-weight' : 1,
      'line-height' : 1,
      'opacity'     : 1,
      'z-index'     : 1,
      'zoom'        : 1
    },
    fragmentRE = /^\s*<(\w+|!)[^>]*>/,
    singleTagRE = /^<(\w+)\s*\/?>(?:<\/\1>|)$/,
    tagExpanderRE = /<(?!area|br|col|embed|hr|img|input|link|meta|param)(([\w:]+)[^>]*)\/>/ig,
    rootNodeRE = /^(?:body|html)$/i,
    capitalRE = /([A-Z])/g,
    
    // special attributes that should be get/set via method calls
    methodAttributes = ['val', 'css', 'html', 'text', 'data', 'width', 'height', 'offset'],
    adjacencyOperators = ['after', 'prepend', 'before', 'append'],
    table = createElement('table'),
    tableRow = createElement('tr'),
    containers = {
      '*'    : createElement('div'),
      'tbody': table,
      'td'   : tableRow,
      'tfoot': table,
      'th'   : tableRow,
      'thead': table,
      'tr'   : createElement('tbody')
    },
    readyRE = /complete|loaded|interactive/,
    simpleSelectorRE = /^[\w-]*$/,
    
    class2type = (function c2t (class2type, toClassString) {
      
      // boolean number string function array date regexp object error
      
      class2type[toClassString(!0)]         = 'boolean';
      class2type[toClassString('boo')]      = 'string';
      class2type[toClassString(/boo/)]      = 'regexp';
      class2type[toClassString(0)]          = 'number';
      class2type[toClassString([])]         = 'array';
      class2type[toClassString(c2t)]        = 'function';
      class2type[toClassString(class2type)] = 'object';
      class2type[toClassString(new Date)]   = 'date';
      class2type[toClassString(new Error)]  = 'error';
      
      return class2type;
    })({}, toClassString),
    
    camelize   = lodash.camelCase, 
    uniq       = lodash.unique,
    tempParent = createElement('div'),
    propMap = {
      'cellpadding'    : 'cellPadding',
      'cellspacing'    : 'cellSpacing',
      'class'          : 'className',
      'colspan'        : 'colSpan',
      'contenteditable': 'contentEditable',
      'for'            : 'htmlFor',
      'frameborder'    : 'frameBorder',
      'maxlength'      : 'maxLength',
      'readonly'       : 'readOnly',
      'rowspan'        : 'rowSpan',
      'tabindex'       : 'tabIndex',
      'usemap'         : 'useMap'
    },
    
    compact       = lodash.compact, 
    dasherize     = lodash.kebabCase, 
    extend        = lodash.merge,
    flatten       = lodash.flatten, 
    isArray       = q.test.isarray,
    isFunction    = lodash.isFunction,
    isObject      = lodash.isObject,
    isPlainObject = lodash.isPlainObject, 
    likeArray     = q.test.isarraylike, 
    traverseNode  = q.dom.traverse, 
    
    grepfmap = {
      'false': function (node, pos, ls) {
        return this.f.apply(this.x, arguments);
      },
      'true' : function (node, pos, ls) {
        return !this.f.apply(this.x, arguments);
      }
    };
  
  var children = supportz[CHILDREN] ? 
    (function (node) { return aslice(node[CHILDREN], 0); }): 
    (function (node) { return afilter(node[CHILDNODES], cb_nodetype1); });
  
  zepto.matches = function(element, selector) {
    if (!selector || !element || element.nodeType !== 1) return false
    var matchesSelector = element.webkitMatchesSelector || element.mozMatchesSelector ||
      element.oMatchesSelector || element.matchesSelector
    if (matchesSelector) return matchesSelector.call(element, selector)
      // fall back to performing a selector:
    var match, parent = element.parentNode,
      temp = !parent
    if (temp)(parent = tempParent).appendChild(element)
    match = ~zepto.qsa(parent, selector).indexOf(element)
    temp && tempParent.removeChild(element)
    return match
  }

  // `$.zepto.fragment` takes a html string and an optional tag name
  // to generate DOM nodes nodes from the given html string.
  // The generated DOM nodes are returned as an array.
  // This function can be overriden in plugins for example to make
  // it compatible with browsers that don't support the DOM fully.
  zepto.fragment = function(html, name, properties) {
    var dom, nodes, container
      // A special case optimization for a single tag
    if (singleTagRE.test(html)) dom = $(createElement(RegExp.$1))
    if (!dom) {
      if (html.replace) html = html.replace(tagExpanderRE, "<$1></$2>")
      if (name === undefined) name = fragmentRE.test(html) && RegExp.$1
      if (!(name in containers)) name = '*'
      container = containers[name]
      container.innerHTML = '' + html
      dom = $.each(aslice(container.childNodes, 0), function() {
        container.removeChild(this)
      })
    }
    if (isPlainObject(properties)) {
      nodes = $(dom)
      $.each(properties, function(key, value) {
        if (methodAttributes.indexOf(key) > -1) nodes[key](value)
        else nodes.attr(key, value)
      })
    }
    return dom
  }
  
  // `$.zepto.Z` swaps out the prototype of the given `dom` array
  // of nodes with `$.fn` and thus supplying all the Zepto functions
  // to the array. Note that `__proto__` is not supported on Internet
  // Explorer. This method can be overriden in plugins.
  zepto.Z = function(dom, selector) {
    
    dom || (dom = []);
    dom.__proto__ = $.fn;
    dom.selector = selector || '';
    
    return dom;
  }
  // `$.zepto.isZ` should return `true` if the given object is a Zepto
  // collection. This method can be overriden in plugins.
  zepto.isZ = function(object) {
    return object instanceof zepto.Z
    }
  // `$.zepto.init` is Zepto's counterpart to jQuery's `$.fn.init` and
  // takes a CSS selector and an optional context (and handles various
  // special cases).
  // This method can be overriden in plugins.
  zepto.init = function(selector, context) {
    var dom
      // If nothing given, return an empty Zepto collection
    if (!selector) return zepto.Z()
      // Optimize for string selectors
    else if (typeof selector == 'string') {
      selector = selector.trim()
      // If it's a html fragment, create nodes from it
      // Note: In both Chrome 21 and Firefox 15, DOM error 12
      // is thrown if the fragment doesn't begin with <
      if (selector[0] == '<' && fragmentRE.test(selector))
        dom = zepto.fragment(selector, RegExp.$1, context), selector = NULL
        // If there's a context, create a collection on that context first, and select
        // nodes from there
      else if (context !== undefined) return $(context).find(selector)
        // If it's a CSS selector, use it to select nodes.
      else dom = zepto.qsa(document, selector)
    }
    // If a function is given, call it when the DOM is ready
    else if (isFunction(selector)) return $(document).ready(selector)
      // If a Zepto collection is given, just return it
    else if (zepto.isZ(selector)) return selector
    else {
      // normalize array if an array of nodes is given
      if (isArray(selector)) dom = compact(selector)
        // Wrap DOM nodes.
      else if (isObject(selector))
        dom = [selector], selector = NULL
        // If it's a html fragment, create nodes from it
      else if (fragmentRE.test(selector))
        dom = zepto.fragment(selector.trim(), RegExp.$1, context), selector = NULL
        // If there's a context, create a collection on that context first, and select
        // nodes from there
      else if (context !== undefined) return $(context).find(selector)
        // And last but no least, if it's a CSS selector, use it to select nodes.
      else dom = zepto.qsa(document, selector)
    }
    // create a new Zepto collection from the nodes found
    return zepto.Z(dom, selector)
  }
  // `$` will be the base `Zepto` object. When calling this
  // function just call `$.zepto.init, which makes the implementation
  // details of selecting nodes and creating Zepto collections
  // patchable in plugins.
  $ = function(selector, context) {
    return zepto.init(selector, context)
    }

  // Copy all but undefined properties from one or more
  // objects to the `target` object.
  $.extend = function(target) {
    var deep, args = aslice(arguments, 1)
    if (typeof target == 'boolean') {
      deep = target
      target = args.shift()
    }
    args.forEach(function(arg) {
      extend(target, arg, deep)
    })
    return target
  }
  // `$.zepto.qsa` is Zepto's CSS selector implementation which
  // uses `document.querySelectorAll` and optimizes for some special cases, like `#id`.
  // This method can be overriden in plugins.
  zepto.qsa = function(element, selector) {
    var found,
      maybeID = selector[0] == '#',
      maybeClass = !maybeID && selector[0] == '.',
      nameOnly = maybeID || maybeClass ? selector.slice(1) : selector, // Ensure that a 1 char tag name still gets checked
      isSimple = simpleSelectorRE.test(nameOnly)
    return (isDocument(element) && isSimple && maybeID) ?
      ((found = element.getElementById(nameOnly)) ? [found] : []) :
      (element.nodeType !== 1 && element.nodeType !== 9) ? [] :
      aslice(
        isSimple && !maybeID ?
        maybeClass ? element.getElementsByClassName(nameOnly) : // If it's simple, it could be a class
        element.getElementsByTagName(selector) : // Or a tag
        element.querySelectorAll(selector),  // Or it's not simple, and we need to query all
        0
      )
  }
  
  paste($, {
    
    'camelCase': camelize,
    'each': coreach,
    'expr': {},
    'grep': basegrep,
    'isArray': isArray,
    'isFunction': isFunction,
    'isPlainObject': isPlainObject,
    'isWindow': isWindow,
    'parseJSON': JSON.parse,
    'support': supportz,
    'trim': cortrim,
    'type': type,
    'uuid': 0,
    'zepto': zepto,
    
    'isEmptyObject': function(node) {
      var field
      for (field in node) return false;
      return true;
    },
    'inArray': function(elem, array, i) {
      return corindexof(array, elem, i);
    },

    'map': function(elements, callback) {
      var value, values = [],
        i, key
      if (likeArray(elements))
        for (i = 0; i < elements.length; i++) {
          value = callback(elements[i], i)
          if (value != NULL) values.push(value)
        } else
        for (key in elements) {
          value = callback(elements[key], key)
          if (value != NULL) values.push(value)
        }
      return flatten(values)
    }
  });

  $.contains = (function(supportz) {
    // container, element
    return supportz[COMPAREDOCUMENTPOSITION] ?
      (function(pnode, node) {
        return 16 === (pnode[COMPAREDOCUMENTPOSITION](node) & 16);
      }) :
      (supportz[CONTAINS] ?
        (function(pnode, node) {
          return (node !== pnode) && pnode[CONTAINS](node);
        }) :
        (function(pnode, node) {
          if (node === pnode) return false;
          for (;node = node.parentNode;)
            if (pnode === node) return true;
          return false;
        }));
    })(supportz);
  
  // Define methods that will be available on all
  // Zepto collections
  $.fn = {

    // Because a collection acts like an array
    // copy over these useful array functions.
    'concat'  : pA.concat,
    'forEach' : pA.forEach,
    'indexOf' : pA.indexOf,
    'push'    : pA.push,
    'reduce'  : pA.reduce,
    'sort'    : pA.sort,
    
    // `map` and `slice` in the jQuery API work differently
    // from their array counterparts
    map: function(fn) {
      return $(amap(this, function(el, i) {
        return fn.call(el, i, el)
      }))
    },
    slice: function () {
      return $(aslice_(this, arguments))
    },
    ready: q.dom.ready,
    get: function(idx) {
      return (idx == NULL) ? aslice(this, 0) : this[idx >= 0 ? idx : idx + this.length]
    },
    toArray: function() {
      return this.get();
    },
    size: function() {
      return this.length;
    },
    remove: function() {
      return this.each(function() {
        if (NULL != this.parentNode)
          this.parentNode.removeChild(this)
      })
    },
    each: function(callback) {
      return pA.every.call(this, function(el, idx) {
        return false !== callback.call(el, idx, el);
      }), this;
    },
    filter: function(selector) {
      if (isFunction(selector)) return this.not(this.not(selector))
      return $(afilter(this, function(element) {
        return zepto.matches(element, selector)
      }))
    },
    add: function(selector, context) {
      return $(uniq(this.concat($(selector, context))))
    },
    is: function(selector) {
      return this.length > 0 && zepto.matches(this[0], selector)
    },
    not: function(selector) {
      var nodes = []
      if (isFunction(selector) && selector.call !== undefined)
        this.each(function(idx) {
          if (!selector.call(this, idx)) nodes.push(this)
        })
      else {
        var excludes = typeof selector == 'string' ? this.filter(selector) :
          (likeArray(selector) && isFunction(selector.item)) ? aslice(selector, 0) : $(selector)
        this.forEach(function(el) {
          if (excludes.indexOf(el) < 0) nodes.push(el)
        })
      }
      return $(nodes)
    },
    has: function(selector) {
      return this.filter(function() {
        return isObject(selector) ?
          $.contains(this, selector) :
          $(this).find(selector).size()
      })
    },
    eq: function(idx) {
      return idx === -1 ? this.slice(idx) : this.slice(idx, +idx + 1)
    },
    first: function() {
      var el = this[0]
      return el && !isObject(el) ? el : $(el)
    },
    last: function() {
      var el = this[this.length - 1]
      return el && !isObject(el) ? el : $(el)
    },
    find: function(selector) {
      var result, $this = this
      if (!selector) result = []
      else if (typeof selector == 'object')
        result = $(selector).filter(function() {
          var node = this
          return pA.some.call($this, function(parent) {
            return $.contains(parent, node)
          })
        })
      else if (this.length == 1) result = $(zepto.qsa(this[0], selector))
      else result = this.map(function() {
        return zepto.qsa(this, selector)
      })
      return result
    },
    closest: function(selector, context) {
      var node = this[0],
        collection = false
      if (typeof selector == 'object') collection = $(selector)
      while (node && !(collection ? collection.indexOf(node) >= 0 : zepto.matches(node, selector)))
        node = node !== context && !isDocument(node) && node.parentNode
      return $(node)
    },
    parents: function(selector) {
      var ancestors = [],
        nodes = this
      while (nodes.length > 0)
        nodes = amap(nodes, function(node) {
          if ((node = node.parentNode) && !isDocument(node) && ancestors.indexOf(node) < 0) {
            ancestors.push(node)
            return node
          }
        })
      return filtered(ancestors, selector)
    },
    parent: function(selector) {
      return filtered(uniq(this.pluck('parentNode')), selector)
    },
    children: function(selector) {
      return filtered(this.map(function() {
        return children(this)
      }), selector)
    },
    contents: function() {
      return this.map(function() {
        return aslice(this.childNodes, 0)
      })
    },
    siblings: function(selector) {
      return filtered(this.map(function(i, el) {
        return afilter(children(el.parentNode), function(child) {
          return child !== el
        })
      }), selector)
    },
    empty: function () {
      return this.each(function() { for (;this.firstChild; this.removeChild(this.firstChild)); });
    },
    // `pluck` is borrowed from Prototype.js
    pluck: function(property) {
      return amap(this, function(el) {  return el[property]; });
    },
    show: function() {
      return this.each(function() {
        this.style.display == "none" && (this.style.display = '')
        if (getComputedProp(this, 'display') == "none")
          this.style.display = defaultDisplay(this.nodeName)
      })
    },
    replaceWith: function(newContent) {
      return this.before(newContent).remove()
    },
    wrap: function(structure) {
      var func = isFunction(structure)
      if (this[0] && !func)
        var dom = $(structure).get(0),
          clone = dom.parentNode || this.length > 1
      return this.each(function(index) {
        $(this).wrapAll(
          func ? structure.call(this, index) :
          clone ? dom.cloneNode(true) : dom
        )
      })
    },
    wrapAll: function(structure) {
      if (this[0]) {
        $(this[0]).before(structure = $(structure))
        var children
          // drill down to the inmost element
        while ((children = structure.children()).length) structure = children.first()
        $(structure).append(this)
      }
      return this
    },
    wrapInner: function(structure) {
      var func = isFunction(structure)
      return this.each(function(index) {
        var self = $(this),
          contents = self.contents(),
          dom = func ? structure.call(this, index) : structure
        contents.length ? contents.wrapAll(dom) : self.append(dom)
      })
    },
    unwrap: function() {
      this.parent().each(function() {
        $(this).replaceWith($(this).children())
      })
      return this
    },
    clone: function() {
      return this.map(function() {
        return this.cloneNode(true)
      })
    },
    hide: function() {
      return this.css("display", "none")
    },
    toggle: function(setting) {
      return this.each(function() {
        var el = $(this);
        (setting === undefined ? el.css("display") == "none" : setting) ? el.show() : el.hide()
      })
    },
    prev: function(selector) {
      return $(this.pluck('previousElementSibling')).filter(selector || '*')
    },
    next: function(selector) {
      return $(this.pluck('nextElementSibling')).filter(selector || '*')
    },
    html: function(html) {
      return 0 in arguments ?
        this.each(function(idx) {
          var originHtml = this.innerHTML
          $(this).empty().append(funcArg(this, html, idx, originHtml))
        }) :
        (0 in this ? this[0].innerHTML : NULL)
    },
    text: function(text) {
      return 0 in arguments ?
        this.each(function(idx) {
          var newText = funcArg(this, text, idx, this.textContent)
          this.textContent = newText == NULL ? '' : '' + newText
        }) :
        (0 in this ? this[0].textContent : NULL)
    },
    attr: function(name, value) {
      var result
      return (typeof name == 'string' && !(1 in arguments)) ?
        (!this.length || this[0].nodeType !== 1 ? undefined :
          (!(result = this[0].getAttribute(name)) && name in this[0]) ? this[0][name] : result
        ) :
        this.each(function(idx) {
          if (this.nodeType !== 1) return
          if (isObject(name))
            for (key in name) setAttribute(this, key, name[key])
          else setAttribute(this, name, funcArg(this, value, idx, this.getAttribute(name)))
        })
    },
    removeAttr: function(name) {
      return this.each(function() {
        this.nodeType === 1 && setAttribute(this, name)
      })
    },
    prop: function(name, value) {
      name = propMap[name] || name
      return (1 in arguments) ?
        this.each(function(idx) {
          this[name] = funcArg(this, value, idx, this[name])
        }) :
        (this[0] && this[0][name])
    },
    data: function(name, value) {
      var attrName = 'data-' + name.replace(capitalRE, '-$1').toLowerCase()
      var data = (1 in arguments) ?
        this.attr(attrName, value) :
        this.attr(attrName)
      return data !== NULL ? deserializeValue(data) : undefined
    },
    val: function(value) {
      return 0 in arguments ?
        this.each(function(idx) {
          this.value = funcArg(this, value, idx, this.value)
        }) :
        (this[0] && (this[0].multiple ?
          $(this[0]).find('option').filter(function() {
            return this.selected
          }).pluck('value') :
          this[0].value))
    },
    offset: function(coordinates) {
      if (coordinates) return this.each(function(index) {
        var $this = $(this),
          coords = funcArg(this, coordinates, index, $this.offset()),
          parentOffset = $this.offsetParent().offset(),
          props = {
            top: coords.top - parentOffset.top,
            left: coords.left - parentOffset.left
          }
        if ($this.css('position') == 'static') props['position'] = 'relative'
        $this.css(props)
      })
      if (!this.length) return NULL
      var obj = this[0].getBoundingClientRect()
      return {
        left: obj.left + window.pageXOffset,
        top: obj.top + window.pageYOffset,
        width: Math.round(obj.width),
        height: Math.round(obj.height)
      }
    },
    css: function(property, value) {
      if (arguments.length < 2) {
        var element = this[0],
          computedStyle = getComputedStyle(element, '')
        if (!element) return
        if (typeof property == 'string')
          return element.style[camelize(property)] || computedStyle.getPropertyValue(property)
        else if (isArray(property)) {
          var props = {}
          $.each(property, function(_, prop) {
            props[prop] = (element.style[camelize(prop)] || computedStyle.getPropertyValue(prop))
          })
          return props
        }
      }
      var css = ''
      if (type(property) == 'string') {
        if (!value && value !== 0)
          this.each(function() {
            this.style.removeProperty(dasherize(property))
          })
        else
          css = dasherize(property) + ":" + maybeAddPx(property, value)
      } else {
        for (key in property)
          if (!property[key] && property[key] !== 0)
            this.each(function() {
              this.style.removeProperty(dasherize(key))
            })
          else
            css += dasherize(key) + ':' + maybeAddPx(key, property[key]) + ';'
      }
      return this.each(function() {
        this.style.cssText += ';' + css
      })
    },
    index: function(element) {
      return element ? this.indexOf($(element)[0]) : this.parent().children().indexOf(this[0])
    },
    hasClass: function(name) {
      if (!name) return false
      return pA.some.call(this, function(el) {
        return this.test(className(el))
      }, classRE(name))
    },
    addClass: function(name) {
      if (!name) return this
      return this.each(function(idx) {
        if (!('className' in this)) return
        classList = []
        var cls = className(this),
          newName = funcArg(this, name, idx, cls)
        newName.split(/\s+/g).forEach(function(klass) {
          if (!$(this).hasClass(klass)) classList.push(klass)
        }, this)
        classList.length && className(this, cls + (cls ? " " : "") + classList.join(" "))
      })
    },
    removeClass: function(name) {
      return this.each(function(idx) {
        if (!('className' in this)) return
        if (name === undefined) return className(this, '')
        classList = className(this)
        funcArg(this, name, idx, classList).split(/\s+/g).forEach(function(klass) {
          classList = classList.replace(classRE(klass), " ")
        })
        className(this, classList.trim())
      })
    },
    toggleClass: function (name, flag) {
      if (!name) return this
      return this.each(function(idx) {
        var $this = $(this),
          names = funcArg(this, name, idx, className(this))
        names.split(/\s+/g).forEach(function(klass) {
          (flag == NULL ? !$this.hasClass(klass) : flag) ?
            $this.addClass(klass) : $this.removeClass(klass)
        })
      })
    },
    scrollTop: function(value) {
      if (!this.length) return
      var hasScrollTop = 'scrollTop' in this[0]
      if (value === undefined) return hasScrollTop ? this[0].scrollTop : this[0].pageYOffset
      return this.each(hasScrollTop ?
        function() {
          this.scrollTop = value
        } :
        function() {
          this.scrollTo(this.scrollX, value)
        })
    },
    scrollLeft: function(value) {
      if (!this.length) return
      var hasScrollLeft = 'scrollLeft' in this[0]
      if (value === undefined) return hasScrollLeft ? this[0].scrollLeft : this[0].pageXOffset
      return this.each(hasScrollLeft ?
        function() {
          this.scrollLeft = value
        } :
        function() {
          this.scrollTo(value, this.scrollY)
        })
    },
    position: function() {
      if (!this.length) return
      var elem = this[0],
        // Get *real* offsetParent
        offsetParent = this.offsetParent(),
        // Get correct offsets
        offset = this.offset(),
        parentOffset = rootNodeRE.test(offsetParent[0].nodeName) ? {
          top: 0,
          left: 0
        } : offsetParent.offset()
        // Subtract element margins
        // note: when an element has margin: auto the offsetLeft and marginLeft
        // are the same in Safari causing offset.left to incorrectly be 0
      offset.top -= parseFloat($(elem).css('margin-top')) || 0
      offset.left -= parseFloat($(elem).css('margin-left')) || 0
      // Add offsetParent borders
      parentOffset.top += parseFloat($(offsetParent[0]).css('border-top-width')) || 0
      parentOffset.left += parseFloat($(offsetParent[0]).css('border-left-width')) || 0
      // Subtract the two offsets
      return {
        top: offset.top - parentOffset.top,
        left: offset.left - parentOffset.left
      }
    },
    offsetParent: function() {
      return this.map(function() {
        var parent = this.offsetParent || getbody()
        while (parent && !rootNodeRE.test(parent.nodeName) && $(parent).css("position") == "static")
          parent = parent.offsetParent
        return parent
      })
    }
  }
  // for now
  $.fn.detach = $.fn.remove
  // Generate the `width` and `height` functions
  ;
  ['width', 'height'].forEach(function(dimension) {
    var dimensionProperty =
      dimension.replace(/./, function(m) {
        return m[0].toUpperCase()
      })
    $.fn[dimension] = function(value) {
      var offset, el = this[0]
      if (value === undefined) return isWindow(el) ? el['inner' + dimensionProperty] :
        isDocument(el) ? el.documentElement['scroll' + dimensionProperty] :
        (offset = this.offset()) && offset[dimension]
      else return this.each(function(idx) {
        el = $(this)
        el.css(dimension, funcArg(this, value, idx, el[dimension]()))
      })
    }
  })

  // Generate the `after`, `prepend`, `before`, `append`,
  // `insertAfter`, `insertBefore`, `appendTo`, and `prependTo` methods.
  adjacencyOperators.forEach(function(operator, operatorIndex) {
    var inside = operatorIndex % 2 //=> prepend, append
    $.fn[operator] = function() {
      // arguments can be nodes, arrays of nodes, Zepto objects and HTML strings
      var argType, nodes = amap(arguments, function(arg) {
          argType = type(arg)
          return argType == "object" || argType == "array" || arg == NULL ?
            arg : zepto.fragment(arg)
        }),
        parent, copyByClone = this.length > 1
      if (nodes.length < 1) return this
      return this.each(function(_, target) {
        parent = inside ? target : target.parentNode
        // convert all methods to a "before" operation
        target = operatorIndex == 0 ? target.nextSibling :
          operatorIndex == 1 ? target.firstChild :
          operatorIndex == 2 ? target :
          NULL
        var parentInDocument = $.contains(document.documentElement, parent)
        nodes.forEach(function(node) {
          if (copyByClone) node = node.cloneNode(true)
          else if (!parent) return $(node).remove()
          parent.insertBefore(node, target)
          if (parentInDocument) traverseNode(node, function() {
            var el = this;
            if (el.nodeName != NULL && el.nodeName.toUpperCase() === 'SCRIPT' &&
              (!el.type || el.type === 'text/javascript') && !el.src)
              window['eval'].call(window, el.innerHTML)
          })
        })
      })
    }
    // after    => insertAfter
    // prepend  => prependTo
    // before   => insertBefore
    // append   => appendTo
    $.fn[inside ? operator + 'To' : 'insert' + (operatorIndex ? 'Before' : 'After')] = function(html) {
      $(html)[operator](this)
      return this
    }
  })
  
  zepto.Z.prototype = $.fn;
  
  // Export internal API functions in the `$.zepto` namespace
  zepto.uniq = uniq;
  zepto.deserializeValue = deserializeValue;  
  
  
  return $;
  
  
  // #helpers
  
  function type (obj) {
    return (NULL == obj) ? ('' + obj) : (class2type[toClassString(obj)] || "object");
  }

  function isWindow (obj) {
    return obj != NULL && obj === obj.window;
  }

  function isDocument (obj) {
    return ~toClassString(obj).toLowerCase().indexOf('document');
  }

  function classRE (name) {
    return (name in classCache) ? classCache[name] : 
      (classCache[name] = new RegExp('(^|\\s)' + name + '(\\s|$)'))
  }

  function maybeAddPx (name, value) {
    return (typeof value == "number" && !cssNumber[dasherize(name)]) ? value + "px" : value
  }
  
  function defaultDisplay (nodeName) {
    
    var element, display
    
    if (!elementDisplay[nodeName]) {
      element = createElement(nodeName);
      getbody().appendChild(element);
      display = getComputedProp(element, 'display');
      element.parentNode.removeChild(element);
      display == "none" && (display = "block");
      elementDisplay[nodeName] = display;
      element = NULL;
    }
    
    return elementDisplay[nodeName]
  }
  
  function filtered(nodes, selector) {
    return (NULL == selector) ? $(nodes) : $(nodes).filter(selector)
  }
  
  function funcArg(context, arg, idx, payload) {
    return isFunction(arg) ? arg.call(context, idx, payload) : arg
  }

  function setAttribute(node, name, value) {
    (value == NULL) ? node.removeAttribute(name) : node.setAttribute(name, value);
  }
  
  // access className property while respecting SVGAnimatedString
  function className(node, value) {
    var klass = node.className || '',
      svg = klass && klass.baseVal !== undefined
    if (value === undefined) return svg ? klass.baseVal : klass
    svg ? (klass.baseVal = value) : (node.className = value)
  }
  
  // "true"  => true
  // "false" => false
  // "null"  => null
  // "42"    => 42
  // "42.5"  => 42.5
  // "08"    => "08"
  // JSON    => parse if valid
  // String  => self
  function deserializeValue(value) {
    var num
    try {
      return value ?
        value == "true" ||
        (value == "false" ? false :
          value == "null" ? NULL :
          !/^0/.test(value) && !isNaN(num = Number(value)) ? num :
          /^[\[\{]/.test(value) ? $.parseJSON(value) :
          value) : value
    } catch (e) {
      return value
    }
  }
    
  function basegrep (ls, callback, binverse, context) {
    return afilter(ls, grepfmap[('' + !!binverse)], {
      'f': callback, 'x': context || ls});
  }
  
  function cb_nodetype1 (node) { return 1 === node.nodeType; }
})(supportz);
