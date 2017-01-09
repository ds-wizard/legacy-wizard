"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0/* () */ = 0,
_1/* $fFromAny()4 */ = function(_/* EXTERNAL */){
  return _0/* GHC.Tuple.() */;
},
_2/* errorIO2 */ = "(function (s) { console.error(s); })",
_3/* errorIO1 */ = function(_4/* slzK */, _/* EXTERNAL */){
  var _5/* slzU */ = eval/* EXTERNAL */(E(_2/* FormEngine.JQuery.errorIO2 */)),
  _6/* slA2 */ = __app1/* EXTERNAL */(E(_5/* slzU */), toJSStr/* EXTERNAL */(E(_4/* slzK */)));
  return _0/* GHC.Tuple.() */;
},
_7/* ++ */ = function(_8/* s3hJ */, _9/* s3hK */){
  var _a/* s3hL */ = E(_8/* s3hJ */);
  return (_a/* s3hL */._==0) ? E(_9/* s3hK */) : new T2(1,_a/* s3hL */.a,new T(function(){
    return B(_7/* GHC.Base.++ */(_a/* s3hL */.b, _9/* s3hK */));
  }));
},
_b/* $fHasChildrenFormElement_go */ = function(_c/*  sc52 */, _d/*  sc53 */){
  while(1){
    var _e/*  $fHasChildrenFormElement_go */ = B((function(_f/* sc52 */, _g/* sc53 */){
      var _h/* sc54 */ = E(_f/* sc52 */);
      if(!_h/* sc54 */._){
        return E(_g/* sc53 */);
      }else{
        var _i/*   sc53 */ = B(_7/* GHC.Base.++ */(_g/* sc53 */, new T(function(){
          var _j/* sc57 */ = E(_h/* sc54 */.a);
          if(!_j/* sc57 */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_j/* sc57 */.c);
          }
        },1)));
        _c/*  sc52 */ = _h/* sc54 */.b;
        _d/*  sc53 */ = _i/*   sc53 */;
        return __continue/* EXTERNAL */;
      }
    })(_c/*  sc52 */, _d/*  sc53 */));
    if(_e/*  $fHasChildrenFormElement_go */!=__continue/* EXTERNAL */){
      return _e/*  $fHasChildrenFormElement_go */;
    }
  }
},
_k/* [] */ = __Z/* EXTERNAL */,
_l/* $fHasChildrenFormElement_$cchildren */ = function(_m/* sc5f */){
  var _n/* sc5g */ = E(_m/* sc5f */);
  switch(_n/* sc5g */._){
    case 0:
      return E(_n/* sc5g */.b);
    case 6:
      return new F(function(){return _b/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_go */(_n/* sc5g */.b, _k/* GHC.Types.[] */);});
      break;
    case 8:
      return E(_n/* sc5g */.b);
    case 9:
      return E(_n/* sc5g */.c);
    case 10:
      return E(_n/* sc5g */.b);
    default:
      return __Z/* EXTERNAL */;
  }
},
_o/* addClass2 */ = "(function (cls, jq) { jq.addClass(cls); return jq; })",
_p/* $wa */ = function(_q/* slQn */, _r/* slQo */, _/* EXTERNAL */){
  var _s/* slQy */ = eval/* EXTERNAL */(E(_o/* FormEngine.JQuery.addClass2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_s/* slQy */), toJSStr/* EXTERNAL */(E(_q/* slQn */)), _r/* slQo */);});
},
_t/* disableJq5 */ = "(function (k, v, jq) { jq.attr(k, v); return jq; })",
_u/* $wa6 */ = function(_v/* slRC */, _w/* slRD */, _x/* slRE */, _/* EXTERNAL */){
  var _y/* slRT */ = eval/* EXTERNAL */(E(_t/* FormEngine.JQuery.disableJq5 */));
  return new F(function(){return __app3/* EXTERNAL */(E(_y/* slRT */), toJSStr/* EXTERNAL */(E(_v/* slRC */)), toJSStr/* EXTERNAL */(E(_w/* slRD */)), _x/* slRE */);});
},
_z/* addClassInside_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.parent(); })");
}),
_A/* addClassInside_f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.last(); })");
}),
_B/* addClassInside_f3 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.children(); })");
}),
_C/* $wa20 */ = function(_D/* slSb */, _E/* slSc */, _F/* slSd */, _/* EXTERNAL */){
  var _G/* slSi */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _F/* slSd */),
  _H/* slSo */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _G/* slSi */),
  _I/* slSr */ = B(_u/* FormEngine.JQuery.$wa6 */(_D/* slSb */, _E/* slSc */, _H/* slSo */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_I/* slSr */));});
},
_J/* appearJq5 */ = "(function (key, val, jq) { jq.css(key, val); return jq; })",
_K/* $wa2 */ = function(_L/* slSM */, _M/* slSN */, _N/* slSO */, _/* EXTERNAL */){
  var _O/* slT3 */ = eval/* EXTERNAL */(E(_J/* FormEngine.JQuery.appearJq5 */));
  return new F(function(){return __app3/* EXTERNAL */(E(_O/* slT3 */), toJSStr/* EXTERNAL */(E(_L/* slSM */)), toJSStr/* EXTERNAL */(E(_M/* slSN */)), _N/* slSO */);});
},
_P/* $wa24 */ = function(_Q/* slTs */, _R/* slTt */, _S/* slTu */, _/* EXTERNAL */){
  var _T/* slTz */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _S/* slTu */),
  _U/* slTF */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _T/* slTz */),
  _V/* slTI */ = B(_K/* FormEngine.JQuery.$wa2 */(_Q/* slTs */, _R/* slTt */, _U/* slTF */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_V/* slTI */));});
},
_W/* appendT2 */ = "(function (tag, jq) { return jq.append(tag); })",
_X/* $wa3 */ = function(_Y/* slPn */, _Z/* slPo */, _/* EXTERNAL */){
  var _10/* slPy */ = eval/* EXTERNAL */(E(_W/* FormEngine.JQuery.appendT2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_10/* slPy */), toJSStr/* EXTERNAL */(E(_Y/* slPn */)), _Z/* slPo */);});
},
_11/* setText2 */ = "(function (txt, jq) { jq.text(txt); return jq; })",
_12/* $wa34 */ = function(_13/* slWf */, _14/* slWg */, _/* EXTERNAL */){
  var _15/* slWl */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _14/* slWg */),
  _16/* slWr */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _15/* slWl */),
  _17/* slWC */ = eval/* EXTERNAL */(E(_11/* FormEngine.JQuery.setText2 */)),
  _18/* slWK */ = __app2/* EXTERNAL */(E(_17/* slWC */), toJSStr/* EXTERNAL */(E(_13/* slWf */)), _16/* slWr */);
  return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), _18/* slWK */);});
},
_19/* appendJq_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq, toJq) { return toJq.append(jq); })");
}),
_1a/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<ul>"));
}),
_1b/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("nav"));
}),
_1c/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<li>"));
}),
_1d/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("id"));
}),
_1e/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<a>"));
}),
_1f/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'stripe stripe-thin\'>"));
}),
_1g/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("display"));
}),
_1h/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("none"));
}),
_1i/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("class"));
}),
_1j/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("inside-bordered"));
}),
_1k/* lvl2 */ = function(_/* EXTERNAL */){
  return new F(function(){return __jsNull/* EXTERNAL */();});
},
_1l/* unsafeDupablePerformIO */ = function(_1m/* s2Wdd */){
  var _1n/* s2Wde */ = B(A1(_1m/* s2Wdd */,_/* EXTERNAL */));
  return E(_1n/* s2Wde */);
},
_1o/* nullValue */ = new T(function(){
  return B(_1l/* GHC.IO.unsafeDupablePerformIO */(_1k/* Haste.Prim.Any.lvl2 */));
}),
_1p/* jsNull */ = new T(function(){
  return E(_1o/* Haste.Prim.Any.nullValue */);
}),
_1q/* onClick2 */ = "(function (ev, jq) { jq.click(ev); })",
_1r/* onClick1 */ = function(_1s/* sluS */, _1t/* sluT */, _/* EXTERNAL */){
  var _1u/* slv5 */ = __createJSFunc/* EXTERNAL */(2, function(_1v/* sluW */, _/* EXTERNAL */){
    var _1w/* sluY */ = B(A2(E(_1s/* sluS */),_1v/* sluW */, _/* EXTERNAL */));
    return _1p/* Haste.Prim.Any.jsNull */;
  }),
  _1x/* slv8 */ = E(_1t/* sluT */),
  _1y/* slvd */ = eval/* EXTERNAL */(E(_1q/* FormEngine.JQuery.onClick2 */)),
  _1z/* slvl */ = __app2/* EXTERNAL */(E(_1y/* slvd */), _1u/* slv5 */, _1x/* slv8 */);
  return _1x/* slv8 */;
},
_1A/* fiDescriptor */ = function(_1B/* s5i9 */){
  var _1C/* s5ia */ = E(_1B/* s5i9 */);
  switch(_1C/* s5ia */._){
    case 0:
      return E(_1C/* s5ia */.a);
    case 1:
      return E(_1C/* s5ia */.a);
    case 2:
      return E(_1C/* s5ia */.a);
    case 3:
      return E(_1C/* s5ia */.a);
    case 4:
      return E(_1C/* s5ia */.a);
    case 5:
      return E(_1C/* s5ia */.a);
    case 6:
      return E(_1C/* s5ia */.a);
    case 7:
      return E(_1C/* s5ia */.a);
    case 8:
      return E(_1C/* s5ia */.a);
    case 9:
      return E(_1C/* s5ia */.a);
    case 10:
      return E(_1C/* s5ia */.a);
    case 11:
      return E(_1C/* s5ia */.a);
    default:
      return E(_1C/* s5ia */.a);
  }
},
_1D/* formItem */ = function(_1E/* sc32 */){
  var _1F/* sc33 */ = E(_1E/* sc32 */);
  switch(_1F/* sc33 */._){
    case 0:
      return E(_1F/* sc33 */.a);
    case 1:
      return E(_1F/* sc33 */.a);
    case 2:
      return E(_1F/* sc33 */.a);
    case 3:
      return E(_1F/* sc33 */.a);
    case 4:
      return E(_1F/* sc33 */.a);
    case 5:
      return E(_1F/* sc33 */.a);
    case 6:
      return E(_1F/* sc33 */.a);
    case 7:
      return E(_1F/* sc33 */.a);
    case 8:
      return E(_1F/* sc33 */.a);
    case 9:
      return E(_1F/* sc33 */.a);
    case 10:
      return E(_1F/* sc33 */.a);
    case 11:
      return E(_1F/* sc33 */.a);
    default:
      return E(_1F/* sc33 */.a);
  }
},
_1G/* itos */ = function(_1H/* sfbi */, _1I/* sfbj */){
  var _1J/* sfbl */ = jsShowI/* EXTERNAL */(_1H/* sfbi */);
  return new F(function(){return _7/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_1J/* sfbl */), _1I/* sfbj */);});
},
_1K/* shows7 */ = 41,
_1L/* shows8 */ = 40,
_1M/* $wshowSignedInt */ = function(_1N/* sfbq */, _1O/* sfbr */, _1P/* sfbs */){
  if(_1O/* sfbr */>=0){
    return new F(function(){return _1G/* GHC.Show.itos */(_1O/* sfbr */, _1P/* sfbs */);});
  }else{
    if(_1N/* sfbq */<=6){
      return new F(function(){return _1G/* GHC.Show.itos */(_1O/* sfbr */, _1P/* sfbs */);});
    }else{
      return new T2(1,_1L/* GHC.Show.shows8 */,new T(function(){
        var _1Q/* sfby */ = jsShowI/* EXTERNAL */(_1O/* sfbr */);
        return B(_7/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_1Q/* sfby */), new T2(1,_1K/* GHC.Show.shows7 */,_1P/* sfbs */)));
      }));
    }
  }
},
_1R/* $fShowInt_$cshow */ = function(_1S/* sffD */){
  return new F(function(){return _1M/* GHC.Show.$wshowSignedInt */(0, E(_1S/* sffD */), _k/* GHC.Types.[] */);});
},
_1T/* $wgo */ = function(_1U/* s5jn */, _1V/* s5jo */){
  var _1W/* s5jp */ = E(_1U/* s5jn */);
  if(!_1W/* s5jp */._){
    return __Z/* EXTERNAL */;
  }else{
    var _1X/* s5jq */ = _1W/* s5jp */.a,
    _1Y/* s5js */ = E(_1V/* s5jo */);
    return (_1Y/* s5js */==1) ? new T2(1,new T(function(){
      return B(_1R/* GHC.Show.$fShowInt_$cshow */(_1X/* s5jq */));
    }),_k/* GHC.Types.[] */) : new T2(1,new T(function(){
      return B(_1R/* GHC.Show.$fShowInt_$cshow */(_1X/* s5jq */));
    }),new T(function(){
      return B(_1T/* FormEngine.FormItem.$wgo */(_1W/* s5jp */.b, _1Y/* s5js */-1|0));
    }));
  }
},
_1Z/* intercalate1 */ = function(_20/* s1WJa */){
  var _21/* s1WJb */ = E(_20/* s1WJa */);
  if(!_21/* s1WJb */._){
    return __Z/* EXTERNAL */;
  }else{
    return new F(function(){return _7/* GHC.Base.++ */(_21/* s1WJb */.a, new T(function(){
      return B(_1Z/* Data.OldList.intercalate1 */(_21/* s1WJb */.b));
    },1));});
  }
},
_22/* numbering2text1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_"));
}),
_23/* prependToAll */ = function(_24/* s1WIX */, _25/* s1WIY */){
  var _26/* s1WIZ */ = E(_25/* s1WIY */);
  return (_26/* s1WIZ */._==0) ? __Z/* EXTERNAL */ : new T2(1,_24/* s1WIX */,new T2(1,_26/* s1WIZ */.a,new T(function(){
    return B(_23/* Data.OldList.prependToAll */(_24/* s1WIX */, _26/* s1WIZ */.b));
  })));
},
_27/* numbering2text */ = function(_28/* s5jx */){
  var _29/* s5jy */ = E(_28/* s5jx */);
  if(!_29/* s5jy */._){
    return __Z/* EXTERNAL */;
  }else{
    var _2a/* s5jD */ = E(_29/* s5jy */.b)+1|0;
    if(0>=_2a/* s5jD */){
      return __Z/* EXTERNAL */;
    }else{
      var _2b/* s5jG */ = B(_1T/* FormEngine.FormItem.$wgo */(_29/* s5jy */.a, _2a/* s5jD */));
      if(!_2b/* s5jG */._){
        return __Z/* EXTERNAL */;
      }else{
        return new F(function(){return _1Z/* Data.OldList.intercalate1 */(new T2(1,_2b/* s5jG */.a,new T(function(){
          return B(_23/* Data.OldList.prependToAll */(_22/* FormEngine.FormItem.numbering2text1 */, _2b/* s5jG */.b));
        })));});
      }
    }
  }
},
_2c/* paneId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("pane_"));
}),
_2d/* paneId */ = function(_2e/* sfOJ */){
  return new F(function(){return _7/* GHC.Base.++ */(_2c/* FormEngine.FormElement.Identifiers.paneId1 */, new T(function(){
    return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_2e/* sfOJ */)))).b));
  },1));});
},
_2f/* tabId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("tab_"));
}),
_2g/* tabId */ = function(_2h/* sfOY */){
  return new F(function(){return _7/* GHC.Base.++ */(_2f/* FormEngine.FormElement.Identifiers.tabId1 */, new T(function(){
    return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_2h/* sfOY */)))).b));
  },1));});
},
_2i/* tabName */ = function(_2j/* sfMw */){
  var _2k/* sfMK */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_2j/* sfMw */)))).a);
  return (_2k/* sfMK */._==0) ? __Z/* EXTERNAL */ : E(_2k/* sfMK */.a);
},
_2l/* appearJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("block"));
}),
_2m/* appearJq3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("display"));
}),
_2n/* eqString */ = function(_2o/* s3mQ */, _2p/* s3mR */){
  while(1){
    var _2q/* s3mS */ = E(_2o/* s3mQ */);
    if(!_2q/* s3mS */._){
      return (E(_2p/* s3mR */)._==0) ? true : false;
    }else{
      var _2r/* s3mY */ = E(_2p/* s3mR */);
      if(!_2r/* s3mY */._){
        return false;
      }else{
        if(E(_2q/* s3mS */.a)!=E(_2r/* s3mY */.a)){
          return false;
        }else{
          _2o/* s3mQ */ = _2q/* s3mS */.b;
          _2p/* s3mR */ = _2r/* s3mY */.b;
          continue;
        }
      }
    }
  }
},
_2s/* $fEqFormElement_$c== */ = function(_2t/* sc4o */, _2u/* sc4p */){
  return new F(function(){return _2n/* GHC.Base.eqString */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_2t/* sc4o */)))).b)), B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_2u/* sc4p */)))).b)));});
},
_2v/* removeClass2 */ = "(function (cls, jq) { jq.removeClass(cls); return jq; })",
_2w/* $wa16 */ = function(_2x/* slPS */, _2y/* slPT */, _/* EXTERNAL */){
  var _2z/* slQ3 */ = eval/* EXTERNAL */(E(_2v/* FormEngine.JQuery.removeClass2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_2z/* slQ3 */), toJSStr/* EXTERNAL */(E(_2x/* slPS */)), _2y/* slPT */);});
},
_2A/* colorizeTabs2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("notcurrent"));
}),
_2B/* colorizeTabs3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("current"));
}),
_2C/* colorizeTabs4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_2D/* select2 */ = "(function (elId) { var res = $(elId); if (res.length === 0) { console.warn(\'empty $ selection \' + elId); }; return res; })",
_2E/* select1 */ = function(_2F/* slL0 */, _/* EXTERNAL */){
  var _2G/* slLa */ = eval/* EXTERNAL */(E(_2D/* FormEngine.JQuery.select2 */));
  return new F(function(){return __app1/* EXTERNAL */(E(_2G/* slLa */), toJSStr/* EXTERNAL */(E(_2F/* slL0 */)));});
},
_2H/* colorizeTabs1 */ = function(_2I/* sha2 */, _2J/* sha3 */, _/* EXTERNAL */){
  var _2K/* sha5 */ = function(_2L/*  sha6 */, _/* EXTERNAL */){
    while(1){
      var _2M/*  sha5 */ = B((function(_2N/* sha6 */, _/* EXTERNAL */){
        var _2O/* sha8 */ = E(_2N/* sha6 */);
        if(!_2O/* sha8 */._){
          return _0/* GHC.Tuple.() */;
        }else{
          var _2P/* sha9 */ = _2O/* sha8 */.a,
          _2Q/* shaa */ = _2O/* sha8 */.b;
          if(!B(_2s/* FormEngine.FormElement.FormElement.$fEqFormElement_$c== */(_2P/* sha9 */, _2I/* sha2 */))){
            var _2R/* shae */ = B(_2E/* FormEngine.JQuery.select1 */(B(_7/* GHC.Base.++ */(_2C/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
              return B(_2g/* FormEngine.FormElement.Identifiers.tabId */(_2P/* sha9 */));
            },1))), _/* EXTERNAL */)),
            _2S/* shaj */ = B(_2w/* FormEngine.JQuery.$wa16 */(_2B/* FormEngine.FormElement.Tabs.colorizeTabs3 */, E(_2R/* shae */), _/* EXTERNAL */)),
            _2T/* shao */ = B(_p/* FormEngine.JQuery.$wa */(_2A/* FormEngine.FormElement.Tabs.colorizeTabs2 */, E(_2S/* shaj */), _/* EXTERNAL */));
            _2L/*  sha6 */ = _2Q/* shaa */;
            return __continue/* EXTERNAL */;
          }else{
            var _2U/* shat */ = B(_2E/* FormEngine.JQuery.select1 */(B(_7/* GHC.Base.++ */(_2C/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
              return B(_2g/* FormEngine.FormElement.Identifiers.tabId */(_2P/* sha9 */));
            },1))), _/* EXTERNAL */)),
            _2V/* shay */ = B(_2w/* FormEngine.JQuery.$wa16 */(_2A/* FormEngine.FormElement.Tabs.colorizeTabs2 */, E(_2U/* shat */), _/* EXTERNAL */)),
            _2W/* shaD */ = B(_p/* FormEngine.JQuery.$wa */(_2B/* FormEngine.FormElement.Tabs.colorizeTabs3 */, E(_2V/* shay */), _/* EXTERNAL */));
            _2L/*  sha6 */ = _2Q/* shaa */;
            return __continue/* EXTERNAL */;
          }
        }
      })(_2L/*  sha6 */, _/* EXTERNAL */));
      if(_2M/*  sha5 */!=__continue/* EXTERNAL */){
        return _2M/*  sha5 */;
      }
    }
  };
  return new F(function(){return _2K/* sha5 */(_2J/* sha3 */, _/* EXTERNAL */);});
},
_2X/* disappearJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("none"));
}),
_2Y/* toTab2 */ = function(_2Z/* shaU */, _/* EXTERNAL */){
  while(1){
    var _30/* shaW */ = E(_2Z/* shaU */);
    if(!_30/* shaW */._){
      return _0/* GHC.Tuple.() */;
    }else{
      var _31/* shb1 */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2X/* FormEngine.JQuery.disappearJq2 */, E(_30/* shaW */.a), _/* EXTERNAL */));
      _2Z/* shaU */ = _30/* shaW */.b;
      continue;
    }
  }
},
_32/* toTab3 */ = function(_33/* shaG */, _/* EXTERNAL */){
  var _34/* shaI */ = E(_33/* shaG */);
  if(!_34/* shaI */._){
    return _k/* GHC.Types.[] */;
  }else{
    var _35/* shaN */ = B(_2E/* FormEngine.JQuery.select1 */(B(_7/* GHC.Base.++ */(_2C/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
      return B(_2d/* FormEngine.FormElement.Identifiers.paneId */(_34/* shaI */.a));
    },1))), _/* EXTERNAL */)),
    _36/* shaQ */ = B(_32/* FormEngine.FormElement.Tabs.toTab3 */(_34/* shaI */.b, _/* EXTERNAL */));
    return new T2(1,_35/* shaN */,_36/* shaQ */);
  }
},
_37/* toTab1 */ = function(_38/* shb4 */, _39/* shb5 */, _/* EXTERNAL */){
  var _3a/* shb9 */ = B(_2E/* FormEngine.JQuery.select1 */(B(_7/* GHC.Base.++ */(_2C/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
    return B(_2d/* FormEngine.FormElement.Identifiers.paneId */(_38/* shb4 */));
  },1))), _/* EXTERNAL */)),
  _3b/* shbc */ = B(_32/* FormEngine.FormElement.Tabs.toTab3 */(_39/* shb5 */, _/* EXTERNAL */)),
  _3c/* shbf */ = B(_2H/* FormEngine.FormElement.Tabs.colorizeTabs1 */(_38/* shb4 */, _39/* shb5 */, _/* EXTERNAL */)),
  _3d/* shbi */ = B(_2Y/* FormEngine.FormElement.Tabs.toTab2 */(_3b/* shbc */, _/* EXTERNAL */)),
  _3e/* shbn */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2l/* FormEngine.JQuery.appearJq2 */, E(_3a/* shb9 */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_3f/* $wa */ = function(_3g/* shbq */, _3h/* shbr */, _3i/* shbs */, _/* EXTERNAL */){
  var _3j/* shbu */ = B(_X/* FormEngine.JQuery.$wa3 */(_1a/* FormEngine.FormElement.Tabs.lvl */, _3i/* shbs */, _/* EXTERNAL */)),
  _3k/* shbz */ = E(_B/* FormEngine.JQuery.addClassInside_f3 */),
  _3l/* shbC */ = __app1/* EXTERNAL */(_3k/* shbz */, E(_3j/* shbu */)),
  _3m/* shbF */ = E(_A/* FormEngine.JQuery.addClassInside_f2 */),
  _3n/* shbI */ = __app1/* EXTERNAL */(_3m/* shbF */, _3l/* shbC */),
  _3o/* shbL */ = B(_p/* FormEngine.JQuery.$wa */(_1b/* FormEngine.FormElement.Tabs.lvl1 */, _3n/* shbI */, _/* EXTERNAL */)),
  _3p/* shbO */ = function(_/* EXTERNAL */, _3q/* shbQ */){
    var _3r/* shbW */ = __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_3q/* shbQ */)),
    _3s/* shbZ */ = B(_X/* FormEngine.JQuery.$wa3 */(_1f/* FormEngine.FormElement.Tabs.lvl5 */, _3r/* shbW */, _/* EXTERNAL */)),
    _3t/* shc2 */ = E(_3g/* shbq */);
    if(!_3t/* shc2 */._){
      return _3s/* shbZ */;
    }else{
      var _3u/* shc5 */ = E(_3h/* shbr */);
      if(!_3u/* shc5 */._){
        return _3s/* shbZ */;
      }else{
        var _3v/* shc8 */ = B(A1(_3u/* shc5 */.a,_/* EXTERNAL */)),
        _3w/* shcf */ = E(_19/* FormEngine.JQuery.appendJq_f1 */),
        _3x/* shci */ = __app2/* EXTERNAL */(_3w/* shcf */, E(_3v/* shc8 */), E(_3s/* shbZ */)),
        _3y/* shcm */ = B(_C/* FormEngine.JQuery.$wa20 */(_1d/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
          return B(_2d/* FormEngine.FormElement.Identifiers.paneId */(_3t/* shc2 */.a));
        },1), _3x/* shci */, _/* EXTERNAL */)),
        _3z/* shcr */ = B(_P/* FormEngine.JQuery.$wa24 */(_1g/* FormEngine.FormElement.Tabs.lvl6 */, _1h/* FormEngine.FormElement.Tabs.lvl7 */, E(_3y/* shcm */), _/* EXTERNAL */)),
        _3A/* shcw */ = B(_C/* FormEngine.JQuery.$wa20 */(_1i/* FormEngine.FormElement.Tabs.lvl8 */, _1j/* FormEngine.FormElement.Tabs.lvl9 */, E(_3z/* shcr */), _/* EXTERNAL */)),
        _3B/* shcz */ = function(_3C/*  shcA */, _3D/*  shcB */, _3E/*  shcC */, _/* EXTERNAL */){
          while(1){
            var _3F/*  shcz */ = B((function(_3G/* shcA */, _3H/* shcB */, _3I/* shcC */, _/* EXTERNAL */){
              var _3J/* shcE */ = E(_3G/* shcA */);
              if(!_3J/* shcE */._){
                return _3I/* shcC */;
              }else{
                var _3K/* shcH */ = E(_3H/* shcB */);
                if(!_3K/* shcH */._){
                  return _3I/* shcC */;
                }else{
                  var _3L/* shcK */ = B(A1(_3K/* shcH */.a,_/* EXTERNAL */)),
                  _3M/* shcS */ = __app2/* EXTERNAL */(_3w/* shcf */, E(_3L/* shcK */), E(_3I/* shcC */)),
                  _3N/* shcW */ = B(_C/* FormEngine.JQuery.$wa20 */(_1d/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
                    return B(_2d/* FormEngine.FormElement.Identifiers.paneId */(_3J/* shcE */.a));
                  },1), _3M/* shcS */, _/* EXTERNAL */)),
                  _3O/* shd1 */ = B(_P/* FormEngine.JQuery.$wa24 */(_1g/* FormEngine.FormElement.Tabs.lvl6 */, _1h/* FormEngine.FormElement.Tabs.lvl7 */, E(_3N/* shcW */), _/* EXTERNAL */)),
                  _3P/* shd6 */ = B(_C/* FormEngine.JQuery.$wa20 */(_1i/* FormEngine.FormElement.Tabs.lvl8 */, _1j/* FormEngine.FormElement.Tabs.lvl9 */, E(_3O/* shd1 */), _/* EXTERNAL */));
                  _3C/*  shcA */ = _3J/* shcE */.b;
                  _3D/*  shcB */ = _3K/* shcH */.b;
                  _3E/*  shcC */ = _3P/* shd6 */;
                  return __continue/* EXTERNAL */;
                }
              }
            })(_3C/*  shcA */, _3D/*  shcB */, _3E/*  shcC */, _/* EXTERNAL */));
            if(_3F/*  shcz */!=__continue/* EXTERNAL */){
              return _3F/*  shcz */;
            }
          }
        };
        return new F(function(){return _3B/* shcz */(_3t/* shc2 */.b, _3u/* shc5 */.b, _3A/* shcw */, _/* EXTERNAL */);});
      }
    }
  },
  _3Q/* shd9 */ = E(_3g/* shbq */);
  if(!_3Q/* shd9 */._){
    return new F(function(){return _3p/* shbO */(_/* EXTERNAL */, _3o/* shbL */);});
  }else{
    var _3R/* shda */ = _3Q/* shd9 */.a,
    _3S/* shde */ = B(_X/* FormEngine.JQuery.$wa3 */(_1c/* FormEngine.FormElement.Tabs.lvl2 */, E(_3o/* shbL */), _/* EXTERNAL */)),
    _3T/* shdk */ = B(_C/* FormEngine.JQuery.$wa20 */(_1d/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
      return B(_2g/* FormEngine.FormElement.Identifiers.tabId */(_3R/* shda */));
    },1), E(_3S/* shde */), _/* EXTERNAL */)),
    _3U/* shdq */ = __app1/* EXTERNAL */(_3k/* shbz */, E(_3T/* shdk */)),
    _3V/* shdu */ = __app1/* EXTERNAL */(_3m/* shbF */, _3U/* shdq */),
    _3W/* shdx */ = B(_X/* FormEngine.JQuery.$wa3 */(_1e/* FormEngine.FormElement.Tabs.lvl4 */, _3V/* shdu */, _/* EXTERNAL */)),
    _3X/* shdD */ = B(_1r/* FormEngine.JQuery.onClick1 */(function(_3Y/* shdA */, _/* EXTERNAL */){
      return new F(function(){return _37/* FormEngine.FormElement.Tabs.toTab1 */(_3R/* shda */, _3Q/* shd9 */, _/* EXTERNAL */);});
    }, _3W/* shdx */, _/* EXTERNAL */)),
    _3Z/* shdJ */ = B(_12/* FormEngine.JQuery.$wa34 */(new T(function(){
      return B(_2i/* FormEngine.FormElement.Identifiers.tabName */(_3R/* shda */));
    },1), E(_3X/* shdD */), _/* EXTERNAL */)),
    _40/* shdO */ = E(_z/* FormEngine.JQuery.addClassInside_f1 */),
    _41/* shdR */ = __app1/* EXTERNAL */(_40/* shdO */, E(_3Z/* shdJ */)),
    _42/* shdU */ = function(_43/*  shdV */, _44/*  shdW */, _45/*  sh5S */, _/* EXTERNAL */){
      while(1){
        var _46/*  shdU */ = B((function(_47/* shdV */, _48/* shdW */, _49/* sh5S */, _/* EXTERNAL */){
          var _4a/* shdY */ = E(_47/* shdV */);
          if(!_4a/* shdY */._){
            return _48/* shdW */;
          }else{
            var _4b/* she0 */ = _4a/* shdY */.a,
            _4c/* she2 */ = B(_X/* FormEngine.JQuery.$wa3 */(_1c/* FormEngine.FormElement.Tabs.lvl2 */, _48/* shdW */, _/* EXTERNAL */)),
            _4d/* she8 */ = B(_C/* FormEngine.JQuery.$wa20 */(_1d/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
              return B(_2g/* FormEngine.FormElement.Identifiers.tabId */(_4b/* she0 */));
            },1), E(_4c/* she2 */), _/* EXTERNAL */)),
            _4e/* shee */ = __app1/* EXTERNAL */(_3k/* shbz */, E(_4d/* she8 */)),
            _4f/* shei */ = __app1/* EXTERNAL */(_3m/* shbF */, _4e/* shee */),
            _4g/* shel */ = B(_X/* FormEngine.JQuery.$wa3 */(_1e/* FormEngine.FormElement.Tabs.lvl4 */, _4f/* shei */, _/* EXTERNAL */)),
            _4h/* sher */ = B(_1r/* FormEngine.JQuery.onClick1 */(function(_4i/* sheo */, _/* EXTERNAL */){
              return new F(function(){return _37/* FormEngine.FormElement.Tabs.toTab1 */(_4b/* she0 */, _3Q/* shd9 */, _/* EXTERNAL */);});
            }, _4g/* shel */, _/* EXTERNAL */)),
            _4j/* shex */ = B(_12/* FormEngine.JQuery.$wa34 */(new T(function(){
              return B(_2i/* FormEngine.FormElement.Identifiers.tabName */(_4b/* she0 */));
            },1), E(_4h/* sher */), _/* EXTERNAL */)),
            _4k/* sheD */ = __app1/* EXTERNAL */(_40/* shdO */, E(_4j/* shex */)),
            _4l/*   sh5S */ = _/* EXTERNAL */;
            _43/*  shdV */ = _4a/* shdY */.b;
            _44/*  shdW */ = _4k/* sheD */;
            _45/*  sh5S */ = _4l/*   sh5S */;
            return __continue/* EXTERNAL */;
          }
        })(_43/*  shdV */, _44/*  shdW */, _45/*  sh5S */, _/* EXTERNAL */));
        if(_46/*  shdU */!=__continue/* EXTERNAL */){
          return _46/*  shdU */;
        }
      }
    },
    _4m/* sheG */ = B(_42/* shdU */(_3Q/* shd9 */.b, _41/* shdR */, _/* EXTERNAL */, _/* EXTERNAL */));
    return new F(function(){return _3p/* shbO */(_/* EXTERNAL */, _4m/* sheG */);});
  }
},
_4n/* mouseleave2 */ = "(function (jq) { jq.mouseleave(); })",
_4o/* $wa14 */ = function(_4p/* slwz */, _/* EXTERNAL */){
  var _4q/* slwE */ = eval/* EXTERNAL */(E(_4n/* FormEngine.JQuery.mouseleave2 */)),
  _4r/* slwM */ = __app1/* EXTERNAL */(E(_4q/* slwE */), _4p/* slwz */);
  return _4p/* slwz */;
},
_4s/* click2 */ = "(function (jq) { jq.click(); })",
_4t/* $wa5 */ = function(_4u/* slxJ */, _/* EXTERNAL */){
  var _4v/* slxO */ = eval/* EXTERNAL */(E(_4s/* FormEngine.JQuery.click2 */)),
  _4w/* slxW */ = __app1/* EXTERNAL */(E(_4v/* slxO */), _4u/* slxJ */);
  return _4u/* slxJ */;
},
_4x/* False */ = false,
_4y/* Nothing */ = __Z/* EXTERNAL */,
_4z/* aboutTab4 */ = 0,
_4A/* aboutTab6 */ = 1000,
_4B/* aboutTab5 */ = new T2(1,_4A/* Form.aboutTab6 */,_k/* GHC.Types.[] */),
_4C/* aboutTab3 */ = new T2(1,_4B/* Form.aboutTab5 */,_4z/* Form.aboutTab4 */),
_4D/* aboutTab8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("About"));
}),
_4E/* aboutTab7 */ = new T1(1,_4D/* Form.aboutTab8 */),
_4F/* aboutTab2 */ = {_:0,a:_4E/* Form.aboutTab7 */,b:_4C/* Form.aboutTab3 */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_4y/* GHC.Base.Nothing */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_4G/* aboutTab1 */ = new T2(7,_4F/* Form.aboutTab2 */,_k/* GHC.Types.[] */),
_4H/* aboutTab */ = new T3(0,_4G/* Form.aboutTab1 */,_k/* GHC.Types.[] */,_4x/* GHC.Types.False */),
_4I/* aboutTabPaneJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("  <div>    <p>      Questionnaire generated from precompiler JSON of <a href=\"https://github.com/CCMi-FIT/ds-km\" target=\"_blank\">Data Stewardship Knowledge Model</a>.    </p>  </div> "));
}),
_4J/* aboutTabPaneJq1 */ = function(_/* EXTERNAL */){
  return new F(function(){return _2E/* FormEngine.JQuery.select1 */(_4I/* Form.aboutTabPaneJq2 */, _/* EXTERNAL */);});
},
_4K/* descSubpaneId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_desc-subpane"));
}),
_4L/* elemChapter */ = function(_4M/* scc1 */){
  while(1){
    var _4N/* scc2 */ = E(_4M/* scc1 */);
    switch(_4N/* scc2 */._){
      case 0:
        return E(_4N/* scc2 */);
      case 1:
        _4M/* scc1 */ = _4N/* scc2 */.c;
        continue;
      case 2:
        _4M/* scc1 */ = _4N/* scc2 */.c;
        continue;
      case 3:
        _4M/* scc1 */ = _4N/* scc2 */.c;
        continue;
      case 4:
        _4M/* scc1 */ = _4N/* scc2 */.d;
        continue;
      case 5:
        _4M/* scc1 */ = _4N/* scc2 */.b;
        continue;
      case 6:
        _4M/* scc1 */ = _4N/* scc2 */.c;
        continue;
      case 7:
        _4M/* scc1 */ = _4N/* scc2 */.c;
        continue;
      case 8:
        _4M/* scc1 */ = _4N/* scc2 */.c;
        continue;
      case 9:
        _4M/* scc1 */ = _4N/* scc2 */.d;
        continue;
      case 10:
        _4M/* scc1 */ = _4N/* scc2 */.c;
        continue;
      case 11:
        _4M/* scc1 */ = _4N/* scc2 */.b;
        continue;
      default:
        _4M/* scc1 */ = _4N/* scc2 */.b;
        continue;
    }
  }
},
_4O/* descSubpaneId */ = function(_4P/* sfMM */){
  return new F(function(){return _7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(B(_4L/* FormEngine.FormElement.FormElement.elemChapter */(_4P/* sfMM */)))))).b)), _4K/* FormEngine.FormElement.Identifiers.descSubpaneId1 */);});
},
_4Q/* descSubpaneParagraphId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_desc-subpane-text"));
}),
_4R/* descSubpaneParagraphId */ = function(_4S/* sfPd */){
  return new F(function(){return _7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(B(_4L/* FormEngine.FormElement.FormElement.elemChapter */(_4S/* sfPd */)))))).b)), _4Q/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId1 */);});
},
_4T/* $fEqOption_$c== */ = function(_4U/* s5oP */, _4V/* s5oQ */){
  var _4W/* s5oR */ = E(_4U/* s5oP */);
  if(!_4W/* s5oR */._){
    var _4X/* s5oS */ = _4W/* s5oR */.a,
    _4Y/* s5oT */ = E(_4V/* s5oQ */);
    if(!_4Y/* s5oT */._){
      return new F(function(){return _2n/* GHC.Base.eqString */(_4X/* s5oS */, _4Y/* s5oT */.a);});
    }else{
      return new F(function(){return _2n/* GHC.Base.eqString */(_4X/* s5oS */, _4Y/* s5oT */.b);});
    }
  }else{
    var _4Z/* s5oZ */ = _4W/* s5oR */.b,
    _50/* s5p1 */ = E(_4V/* s5oQ */);
    if(!_50/* s5p1 */._){
      return new F(function(){return _2n/* GHC.Base.eqString */(_4Z/* s5oZ */, _50/* s5p1 */.a);});
    }else{
      return new F(function(){return _2n/* GHC.Base.eqString */(_4Z/* s5oZ */, _50/* s5p1 */.b);});
    }
  }
},
_51/* $fShowNumbering2 */ = 0,
_52/* $fShowFormElement1 */ = function(_53/* sc5x */, _54/* sc5y */){
  return new F(function(){return _7/* GHC.Base.++ */(B(_55/* FormEngine.FormElement.FormElement.$fShowFormElement_$cshow */(_53/* sc5x */)), _54/* sc5y */);});
},
_56/* $fShowMaybe1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Just "));
}),
_57/* $fShowMaybe3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nothing"));
}),
_58/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SubmitButtonElem id="));
}),
_59/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SaveButtonElem id="));
}),
_5a/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" unit="));
}),
_5b/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NumberElem id="));
}),
_5c/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EmailElem id="));
}),
_5d/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TextElem id="));
}),
_5e/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("StringElem id="));
}),
_5f/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ChapterElem id="));
}),
_5g/* shows5 */ = 34,
_5h/* lvl16 */ = new T2(1,_5g/* GHC.Show.shows5 */,_k/* GHC.Types.[] */),
_5i/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MultipleGroupElem id="));
}),
_5j/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" children: "));
}),
_5k/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("OptionalGroupElem id="));
}),
_5l/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SimpleGroupElem id="));
}),
_5m/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" value="));
}),
_5n/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ListElem id="));
}),
_5o/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ChoiceElem id="));
}),
_5p/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("InfoElem id="));
}),
_5q/* showList__1 */ = 44,
_5r/* showList__2 */ = 93,
_5s/* showList__3 */ = 91,
_5t/* showList__ */ = function(_5u/* sfc2 */, _5v/* sfc3 */, _5w/* sfc4 */){
  var _5x/* sfc5 */ = E(_5v/* sfc3 */);
  if(!_5x/* sfc5 */._){
    return new F(function(){return unAppCStr/* EXTERNAL */("[]", _5w/* sfc4 */);});
  }else{
    var _5y/* sfch */ = new T(function(){
      var _5z/* sfcg */ = new T(function(){
        var _5A/* sfc9 */ = function(_5B/* sfca */){
          var _5C/* sfcb */ = E(_5B/* sfca */);
          if(!_5C/* sfcb */._){
            return E(new T2(1,_5r/* GHC.Show.showList__2 */,_5w/* sfc4 */));
          }else{
            var _5D/* sfcf */ = new T(function(){
              return B(A2(_5u/* sfc2 */,_5C/* sfcb */.a, new T(function(){
                return B(_5A/* sfc9 */(_5C/* sfcb */.b));
              })));
            });
            return new T2(1,_5q/* GHC.Show.showList__1 */,_5D/* sfcf */);
          }
        };
        return B(_5A/* sfc9 */(_5x/* sfc5 */.b));
      });
      return B(A2(_5u/* sfc2 */,_5x/* sfc5 */.a, _5z/* sfcg */));
    });
    return new T2(1,_5s/* GHC.Show.showList__3 */,_5y/* sfch */);
  }
},
_5E/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!!: negative index"));
}),
_5F/* prel_list_str */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude."));
}),
_5G/* lvl2 */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_5F/* GHC.List.prel_list_str */, _5E/* GHC.List.lvl1 */));
}),
_5H/* negIndex */ = new T(function(){
  return B(err/* EXTERNAL */(_5G/* GHC.List.lvl2 */));
}),
_5I/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!!: index too large"));
}),
_5J/* lvl4 */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_5F/* GHC.List.prel_list_str */, _5I/* GHC.List.lvl3 */));
}),
_5K/* !!1 */ = new T(function(){
  return B(err/* EXTERNAL */(_5J/* GHC.List.lvl4 */));
}),
_5L/* poly_$wgo2 */ = function(_5M/* s9uh */, _5N/* s9ui */){
  while(1){
    var _5O/* s9uj */ = E(_5M/* s9uh */);
    if(!_5O/* s9uj */._){
      return E(_5K/* GHC.List.!!1 */);
    }else{
      var _5P/* s9um */ = E(_5N/* s9ui */);
      if(!_5P/* s9um */){
        return E(_5O/* s9uj */.a);
      }else{
        _5M/* s9uh */ = _5O/* s9uj */.b;
        _5N/* s9ui */ = _5P/* s9um */-1|0;
        continue;
      }
    }
  }
},
_5Q/* $w!! */ = function(_5R/* s9uo */, _5S/* s9up */){
  if(_5S/* s9up */>=0){
    return new F(function(){return _5L/* GHC.List.poly_$wgo2 */(_5R/* s9uo */, _5S/* s9up */);});
  }else{
    return E(_5H/* GHC.List.negIndex */);
  }
},
_5T/* asciiTab59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ACK"));
}),
_5U/* asciiTab58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BEL"));
}),
_5V/* asciiTab57 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BS"));
}),
_5W/* asciiTab33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SP"));
}),
_5X/* asciiTab32 */ = new T2(1,_5W/* GHC.Show.asciiTab33 */,_k/* GHC.Types.[] */),
_5Y/* asciiTab34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("US"));
}),
_5Z/* asciiTab31 */ = new T2(1,_5Y/* GHC.Show.asciiTab34 */,_5X/* GHC.Show.asciiTab32 */),
_60/* asciiTab35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RS"));
}),
_61/* asciiTab30 */ = new T2(1,_60/* GHC.Show.asciiTab35 */,_5Z/* GHC.Show.asciiTab31 */),
_62/* asciiTab36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GS"));
}),
_63/* asciiTab29 */ = new T2(1,_62/* GHC.Show.asciiTab36 */,_61/* GHC.Show.asciiTab30 */),
_64/* asciiTab37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FS"));
}),
_65/* asciiTab28 */ = new T2(1,_64/* GHC.Show.asciiTab37 */,_63/* GHC.Show.asciiTab29 */),
_66/* asciiTab38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ESC"));
}),
_67/* asciiTab27 */ = new T2(1,_66/* GHC.Show.asciiTab38 */,_65/* GHC.Show.asciiTab28 */),
_68/* asciiTab39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SUB"));
}),
_69/* asciiTab26 */ = new T2(1,_68/* GHC.Show.asciiTab39 */,_67/* GHC.Show.asciiTab27 */),
_6a/* asciiTab40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EM"));
}),
_6b/* asciiTab25 */ = new T2(1,_6a/* GHC.Show.asciiTab40 */,_69/* GHC.Show.asciiTab26 */),
_6c/* asciiTab41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CAN"));
}),
_6d/* asciiTab24 */ = new T2(1,_6c/* GHC.Show.asciiTab41 */,_6b/* GHC.Show.asciiTab25 */),
_6e/* asciiTab42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETB"));
}),
_6f/* asciiTab23 */ = new T2(1,_6e/* GHC.Show.asciiTab42 */,_6d/* GHC.Show.asciiTab24 */),
_6g/* asciiTab43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SYN"));
}),
_6h/* asciiTab22 */ = new T2(1,_6g/* GHC.Show.asciiTab43 */,_6f/* GHC.Show.asciiTab23 */),
_6i/* asciiTab44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NAK"));
}),
_6j/* asciiTab21 */ = new T2(1,_6i/* GHC.Show.asciiTab44 */,_6h/* GHC.Show.asciiTab22 */),
_6k/* asciiTab45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC4"));
}),
_6l/* asciiTab20 */ = new T2(1,_6k/* GHC.Show.asciiTab45 */,_6j/* GHC.Show.asciiTab21 */),
_6m/* asciiTab46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC3"));
}),
_6n/* asciiTab19 */ = new T2(1,_6m/* GHC.Show.asciiTab46 */,_6l/* GHC.Show.asciiTab20 */),
_6o/* asciiTab47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC2"));
}),
_6p/* asciiTab18 */ = new T2(1,_6o/* GHC.Show.asciiTab47 */,_6n/* GHC.Show.asciiTab19 */),
_6q/* asciiTab48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC1"));
}),
_6r/* asciiTab17 */ = new T2(1,_6q/* GHC.Show.asciiTab48 */,_6p/* GHC.Show.asciiTab18 */),
_6s/* asciiTab49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DLE"));
}),
_6t/* asciiTab16 */ = new T2(1,_6s/* GHC.Show.asciiTab49 */,_6r/* GHC.Show.asciiTab17 */),
_6u/* asciiTab50 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SI"));
}),
_6v/* asciiTab15 */ = new T2(1,_6u/* GHC.Show.asciiTab50 */,_6t/* GHC.Show.asciiTab16 */),
_6w/* asciiTab51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SO"));
}),
_6x/* asciiTab14 */ = new T2(1,_6w/* GHC.Show.asciiTab51 */,_6v/* GHC.Show.asciiTab15 */),
_6y/* asciiTab52 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CR"));
}),
_6z/* asciiTab13 */ = new T2(1,_6y/* GHC.Show.asciiTab52 */,_6x/* GHC.Show.asciiTab14 */),
_6A/* asciiTab53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FF"));
}),
_6B/* asciiTab12 */ = new T2(1,_6A/* GHC.Show.asciiTab53 */,_6z/* GHC.Show.asciiTab13 */),
_6C/* asciiTab54 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VT"));
}),
_6D/* asciiTab11 */ = new T2(1,_6C/* GHC.Show.asciiTab54 */,_6B/* GHC.Show.asciiTab12 */),
_6E/* asciiTab55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LF"));
}),
_6F/* asciiTab10 */ = new T2(1,_6E/* GHC.Show.asciiTab55 */,_6D/* GHC.Show.asciiTab11 */),
_6G/* asciiTab56 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HT"));
}),
_6H/* asciiTab9 */ = new T2(1,_6G/* GHC.Show.asciiTab56 */,_6F/* GHC.Show.asciiTab10 */),
_6I/* asciiTab8 */ = new T2(1,_5V/* GHC.Show.asciiTab57 */,_6H/* GHC.Show.asciiTab9 */),
_6J/* asciiTab7 */ = new T2(1,_5U/* GHC.Show.asciiTab58 */,_6I/* GHC.Show.asciiTab8 */),
_6K/* asciiTab6 */ = new T2(1,_5T/* GHC.Show.asciiTab59 */,_6J/* GHC.Show.asciiTab7 */),
_6L/* asciiTab60 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ENQ"));
}),
_6M/* asciiTab5 */ = new T2(1,_6L/* GHC.Show.asciiTab60 */,_6K/* GHC.Show.asciiTab6 */),
_6N/* asciiTab61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EOT"));
}),
_6O/* asciiTab4 */ = new T2(1,_6N/* GHC.Show.asciiTab61 */,_6M/* GHC.Show.asciiTab5 */),
_6P/* asciiTab62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETX"));
}),
_6Q/* asciiTab3 */ = new T2(1,_6P/* GHC.Show.asciiTab62 */,_6O/* GHC.Show.asciiTab4 */),
_6R/* asciiTab63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("STX"));
}),
_6S/* asciiTab2 */ = new T2(1,_6R/* GHC.Show.asciiTab63 */,_6Q/* GHC.Show.asciiTab3 */),
_6T/* asciiTab64 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SOH"));
}),
_6U/* asciiTab1 */ = new T2(1,_6T/* GHC.Show.asciiTab64 */,_6S/* GHC.Show.asciiTab2 */),
_6V/* asciiTab65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NUL"));
}),
_6W/* asciiTab */ = new T2(1,_6V/* GHC.Show.asciiTab65 */,_6U/* GHC.Show.asciiTab1 */),
_6X/* lvl */ = 92,
_6Y/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\DEL"));
}),
_6Z/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\a"));
}),
_70/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\\\"));
}),
_71/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\SO"));
}),
_72/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\r"));
}),
_73/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\f"));
}),
_74/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\v"));
}),
_75/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\n"));
}),
_76/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\t"));
}),
_77/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\b"));
}),
_78/* $wshowLitChar */ = function(_79/* sfeh */, _7a/* sfei */){
  if(_79/* sfeh */<=127){
    var _7b/* sfel */ = E(_79/* sfeh */);
    switch(_7b/* sfel */){
      case 92:
        return new F(function(){return _7/* GHC.Base.++ */(_70/* GHC.Show.lvl2 */, _7a/* sfei */);});
        break;
      case 127:
        return new F(function(){return _7/* GHC.Base.++ */(_6Y/* GHC.Show.lvl1 */, _7a/* sfei */);});
        break;
      default:
        if(_7b/* sfel */<32){
          var _7c/* sfeo */ = E(_7b/* sfel */);
          switch(_7c/* sfeo */){
            case 7:
              return new F(function(){return _7/* GHC.Base.++ */(_6Z/* GHC.Show.lvl10 */, _7a/* sfei */);});
              break;
            case 8:
              return new F(function(){return _7/* GHC.Base.++ */(_77/* GHC.Show.lvl9 */, _7a/* sfei */);});
              break;
            case 9:
              return new F(function(){return _7/* GHC.Base.++ */(_76/* GHC.Show.lvl8 */, _7a/* sfei */);});
              break;
            case 10:
              return new F(function(){return _7/* GHC.Base.++ */(_75/* GHC.Show.lvl7 */, _7a/* sfei */);});
              break;
            case 11:
              return new F(function(){return _7/* GHC.Base.++ */(_74/* GHC.Show.lvl6 */, _7a/* sfei */);});
              break;
            case 12:
              return new F(function(){return _7/* GHC.Base.++ */(_73/* GHC.Show.lvl5 */, _7a/* sfei */);});
              break;
            case 13:
              return new F(function(){return _7/* GHC.Base.++ */(_72/* GHC.Show.lvl4 */, _7a/* sfei */);});
              break;
            case 14:
              return new F(function(){return _7/* GHC.Base.++ */(_71/* GHC.Show.lvl3 */, new T(function(){
                var _7d/* sfes */ = E(_7a/* sfei */);
                if(!_7d/* sfes */._){
                  return __Z/* EXTERNAL */;
                }else{
                  if(E(_7d/* sfes */.a)==72){
                    return B(unAppCStr/* EXTERNAL */("\\&", _7d/* sfes */));
                  }else{
                    return E(_7d/* sfes */);
                  }
                }
              },1));});
              break;
            default:
              return new F(function(){return _7/* GHC.Base.++ */(new T2(1,_6X/* GHC.Show.lvl */,new T(function(){
                return B(_5Q/* GHC.List.$w!! */(_6W/* GHC.Show.asciiTab */, _7c/* sfeo */));
              })), _7a/* sfei */);});
          }
        }else{
          return new T2(1,_7b/* sfel */,_7a/* sfei */);
        }
    }
  }else{
    var _7e/* sfeR */ = new T(function(){
      var _7f/* sfeC */ = jsShowI/* EXTERNAL */(_79/* sfeh */);
      return B(_7/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_7f/* sfeC */), new T(function(){
        var _7g/* sfeH */ = E(_7a/* sfei */);
        if(!_7g/* sfeH */._){
          return __Z/* EXTERNAL */;
        }else{
          var _7h/* sfeK */ = E(_7g/* sfeH */.a);
          if(_7h/* sfeK */<48){
            return E(_7g/* sfeH */);
          }else{
            if(_7h/* sfeK */>57){
              return E(_7g/* sfeH */);
            }else{
              return B(unAppCStr/* EXTERNAL */("\\&", _7g/* sfeH */));
            }
          }
        }
      },1)));
    });
    return new T2(1,_6X/* GHC.Show.lvl */,_7e/* sfeR */);
  }
},
_7i/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\\""));
}),
_7j/* showLitString */ = function(_7k/* sfeW */, _7l/* sfeX */){
  var _7m/* sfeY */ = E(_7k/* sfeW */);
  if(!_7m/* sfeY */._){
    return E(_7l/* sfeX */);
  }else{
    var _7n/* sff0 */ = _7m/* sfeY */.b,
    _7o/* sff3 */ = E(_7m/* sfeY */.a);
    if(_7o/* sff3 */==34){
      return new F(function(){return _7/* GHC.Base.++ */(_7i/* GHC.Show.lvl11 */, new T(function(){
        return B(_7j/* GHC.Show.showLitString */(_7n/* sff0 */, _7l/* sfeX */));
      },1));});
    }else{
      return new F(function(){return _78/* GHC.Show.$wshowLitChar */(_7o/* sff3 */, new T(function(){
        return B(_7j/* GHC.Show.showLitString */(_7n/* sff0 */, _7l/* sfeX */));
      }));});
    }
  }
},
_55/* $fShowFormElement_$cshow */ = function(_7p/* sc5A */){
  var _7q/* sc5B */ = E(_7p/* sc5A */);
  switch(_7q/* sc5B */._){
    case 0:
      var _7r/* sc5U */ = new T(function(){
        var _7s/* sc5T */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_5j/* FormEngine.FormElement.FormElement.lvl3 */, new T(function(){
            return B(_5t/* GHC.Show.showList__ */(_52/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _7q/* sc5B */.b, _k/* GHC.Types.[] */));
          },1)));
        },1);
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7q/* sc5B */.a)).b)), _7s/* sc5T */));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5f/* FormEngine.FormElement.FormElement.lvl15 */, _7r/* sc5U */);});
      break;
    case 1:
      var _7t/* sc6c */ = new T(function(){
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7q/* sc5B */.a)).b)), new T(function(){
          return B(_7/* GHC.Base.++ */(_5m/* FormEngine.FormElement.FormElement.lvl6 */, _7q/* sc5B */.b));
        },1)));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5e/* FormEngine.FormElement.FormElement.lvl14 */, _7t/* sc6c */);});
      break;
    case 2:
      var _7u/* sc6u */ = new T(function(){
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7q/* sc5B */.a)).b)), new T(function(){
          return B(_7/* GHC.Base.++ */(_5m/* FormEngine.FormElement.FormElement.lvl6 */, _7q/* sc5B */.b));
        },1)));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5d/* FormEngine.FormElement.FormElement.lvl13 */, _7u/* sc6u */);});
      break;
    case 3:
      var _7v/* sc6M */ = new T(function(){
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7q/* sc5B */.a)).b)), new T(function(){
          return B(_7/* GHC.Base.++ */(_5m/* FormEngine.FormElement.FormElement.lvl6 */, _7q/* sc5B */.b));
        },1)));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5c/* FormEngine.FormElement.FormElement.lvl12 */, _7v/* sc6M */);});
      break;
    case 4:
      var _7w/* sc7i */ = new T(function(){
        var _7x/* sc7h */ = new T(function(){
          var _7y/* sc7g */ = new T(function(){
            var _7z/* sc74 */ = new T(function(){
              var _7A/* sc79 */ = new T(function(){
                var _7B/* sc75 */ = E(_7q/* sc5B */.c);
                if(!_7B/* sc75 */._){
                  return E(_57/* GHC.Show.$fShowMaybe3 */);
                }else{
                  return B(_7/* GHC.Base.++ */(_56/* GHC.Show.$fShowMaybe1 */, new T2(1,_5g/* GHC.Show.shows5 */,new T(function(){
                    return B(_7j/* GHC.Show.showLitString */(_7B/* sc75 */.a, _5h/* FormEngine.FormElement.FormElement.lvl16 */));
                  }))));
                }
              },1);
              return B(_7/* GHC.Base.++ */(_5a/* FormEngine.FormElement.FormElement.lvl10 */, _7A/* sc79 */));
            }),
            _7C/* sc7a */ = E(_7q/* sc5B */.b);
            if(!_7C/* sc7a */._){
              return B(_7/* GHC.Base.++ */(_57/* GHC.Show.$fShowMaybe3 */, _7z/* sc74 */));
            }else{
              return B(_7/* GHC.Base.++ */(_56/* GHC.Show.$fShowMaybe1 */, new T(function(){
                return B(_7/* GHC.Base.++ */(B(_1M/* GHC.Show.$wshowSignedInt */(11, E(_7C/* sc7a */.a), _k/* GHC.Types.[] */)), _7z/* sc74 */));
              },1)));
            }
          },1);
          return B(_7/* GHC.Base.++ */(_5m/* FormEngine.FormElement.FormElement.lvl6 */, _7y/* sc7g */));
        },1);
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7q/* sc5B */.a)).b)), _7x/* sc7h */));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5b/* FormEngine.FormElement.FormElement.lvl11 */, _7w/* sc7i */);});
      break;
    case 5:
      return new F(function(){return _7/* GHC.Base.++ */(_5p/* FormEngine.FormElement.FormElement.lvl9 */, new T(function(){
        return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7q/* sc5B */.a)).b));
      },1));});
      break;
    case 6:
      return new F(function(){return _7/* GHC.Base.++ */(_5o/* FormEngine.FormElement.FormElement.lvl8 */, new T(function(){
        return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7q/* sc5B */.a)).b));
      },1));});
      break;
    case 7:
      var _7D/* sc8a */ = new T(function(){
        var _7E/* sc89 */ = new T(function(){
          var _7F/* sc88 */ = new T(function(){
            var _7G/* sc84 */ = E(_7q/* sc5B */.b);
            if(!_7G/* sc84 */._){
              return E(_57/* GHC.Show.$fShowMaybe3 */);
            }else{
              return B(_7/* GHC.Base.++ */(_56/* GHC.Show.$fShowMaybe1 */, new T2(1,_5g/* GHC.Show.shows5 */,new T(function(){
                return B(_7j/* GHC.Show.showLitString */(_7G/* sc84 */.a, _5h/* FormEngine.FormElement.FormElement.lvl16 */));
              }))));
            }
          },1);
          return B(_7/* GHC.Base.++ */(_5m/* FormEngine.FormElement.FormElement.lvl6 */, _7F/* sc88 */));
        },1);
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7q/* sc5B */.a)).b)), _7E/* sc89 */));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5n/* FormEngine.FormElement.FormElement.lvl7 */, _7D/* sc8a */);});
      break;
    case 8:
      var _7H/* sc8t */ = new T(function(){
        var _7I/* sc8s */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_5j/* FormEngine.FormElement.FormElement.lvl3 */, new T(function(){
            return B(_5t/* GHC.Show.showList__ */(_52/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _7q/* sc5B */.b, _k/* GHC.Types.[] */));
          },1)));
        },1);
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7q/* sc5B */.a)).b)), _7I/* sc8s */));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5l/* FormEngine.FormElement.FormElement.lvl5 */, _7H/* sc8t */);});
      break;
    case 9:
      var _7J/* sc8N */ = new T(function(){
        var _7K/* sc8M */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_5j/* FormEngine.FormElement.FormElement.lvl3 */, new T(function(){
            return B(_5t/* GHC.Show.showList__ */(_52/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _7q/* sc5B */.c, _k/* GHC.Types.[] */));
          },1)));
        },1);
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7q/* sc5B */.a)).b)), _7K/* sc8M */));
      },1);
      return new F(function(){return _7/* GHC.Base.++ */(_5k/* FormEngine.FormElement.FormElement.lvl4 */, _7J/* sc8N */);});
      break;
    case 10:
      return new F(function(){return _7/* GHC.Base.++ */(_5i/* FormEngine.FormElement.FormElement.lvl2 */, new T(function(){
        return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7q/* sc5B */.a)).b));
      },1));});
      break;
    case 11:
      return new F(function(){return _7/* GHC.Base.++ */(_59/* FormEngine.FormElement.FormElement.lvl1 */, new T(function(){
        return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7q/* sc5B */.a)).b));
      },1));});
      break;
    default:
      return new F(function(){return _7/* GHC.Base.++ */(_58/* FormEngine.FormElement.FormElement.lvl */, new T(function(){
        return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_7q/* sc5B */.a)).b));
      },1));});
  }
},
_7L/* lvl59 */ = new T2(1,_5g/* GHC.Show.shows5 */,_k/* GHC.Types.[] */),
_7M/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IntValueRule (Int -> Bool)"));
}),
_7N/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ReadOnlyRule"));
}),
_7O/* shows_$cshowList */ = function(_7P/* sff6 */, _7Q/* sff7 */){
  return new T2(1,_5g/* GHC.Show.shows5 */,new T(function(){
    return B(_7j/* GHC.Show.showLitString */(_7P/* sff6 */, new T2(1,_5g/* GHC.Show.shows5 */,_7Q/* sff7 */)));
  }));
},
_7R/* $fShowFormRule_$cshow */ = function(_7S/* s5o7 */){
  var _7T/* s5o8 */ = E(_7S/* s5o7 */);
  switch(_7T/* s5o8 */._){
    case 0:
      var _7U/* s5of */ = new T(function(){
        var _7V/* s5oe */ = new T(function(){
          return B(unAppCStr/* EXTERNAL */(" -> ", new T2(1,_5g/* GHC.Show.shows5 */,new T(function(){
            return B(_7j/* GHC.Show.showLitString */(_7T/* s5o8 */.b, _7L/* FormEngine.FormItem.lvl59 */));
          }))));
        },1);
        return B(_7/* GHC.Base.++ */(B(_5t/* GHC.Show.showList__ */(_7O/* GHC.Show.shows_$cshowList */, _7T/* s5o8 */.a, _k/* GHC.Types.[] */)), _7V/* s5oe */));
      });
      return new F(function(){return unAppCStr/* EXTERNAL */("SumRule @ ", _7U/* s5of */);});
      break;
    case 1:
      var _7W/* s5om */ = new T(function(){
        var _7X/* s5ol */ = new T(function(){
          return B(unAppCStr/* EXTERNAL */(" -> ", new T2(1,_5g/* GHC.Show.shows5 */,new T(function(){
            return B(_7j/* GHC.Show.showLitString */(_7T/* s5o8 */.b, _7L/* FormEngine.FormItem.lvl59 */));
          }))));
        },1);
        return B(_7/* GHC.Base.++ */(B(_5t/* GHC.Show.showList__ */(_7O/* GHC.Show.shows_$cshowList */, _7T/* s5o8 */.a, _k/* GHC.Types.[] */)), _7X/* s5ol */));
      });
      return new F(function(){return unAppCStr/* EXTERNAL */("SumTBsRule @ ", _7W/* s5om */);});
      break;
    case 2:
      var _7Y/* s5ou */ = new T(function(){
        var _7Z/* s5ot */ = new T(function(){
          return B(unAppCStr/* EXTERNAL */(" -> ", new T2(1,_5g/* GHC.Show.shows5 */,new T(function(){
            return B(_7j/* GHC.Show.showLitString */(_7T/* s5o8 */.b, _7L/* FormEngine.FormItem.lvl59 */));
          }))));
        },1);
        return B(_7/* GHC.Base.++ */(new T2(1,_5g/* GHC.Show.shows5 */,new T(function(){
          return B(_7j/* GHC.Show.showLitString */(_7T/* s5o8 */.a, _7L/* FormEngine.FormItem.lvl59 */));
        })), _7Z/* s5ot */));
      });
      return new F(function(){return unAppCStr/* EXTERNAL */("CopyValueRule @ ", _7Y/* s5ou */);});
      break;
    case 3:
      return E(_7N/* FormEngine.FormItem.lvl7 */);
    default:
      return E(_7M/* FormEngine.FormItem.lvl6 */);
  }
},
_80/* identity2element' */ = function(_81/* sjnd */, _82/* sjne */){
  var _83/* sjnf */ = E(_82/* sjne */);
  if(!_83/* sjnf */._){
    return __Z/* EXTERNAL */;
  }else{
    var _84/* sjng */ = _83/* sjnf */.a,
    _85/* sjnv */ = function(_86/* sjnw */){
      var _87/* sjny */ = B(_80/* FormEngine.FormElement.Updating.identity2element' */(_81/* sjnd */, B(_l/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_$cchildren */(_84/* sjng */))));
      if(!_87/* sjny */._){
        return new F(function(){return _80/* FormEngine.FormElement.Updating.identity2element' */(_81/* sjnd */, _83/* sjnf */.b);});
      }else{
        return E(_87/* sjny */);
      }
    },
    _88/* sjnA */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_84/* sjng */)))).c);
    if(!_88/* sjnA */._){
      if(!B(_2n/* GHC.Base.eqString */(_k/* GHC.Types.[] */, _81/* sjnd */))){
        return new F(function(){return _85/* sjnv */(_/* EXTERNAL */);});
      }else{
        return new T1(1,_84/* sjng */);
      }
    }else{
      if(!B(_2n/* GHC.Base.eqString */(_88/* sjnA */.a, _81/* sjnd */))){
        return new F(function(){return _85/* sjnv */(_/* EXTERNAL */);});
      }else{
        return new T1(1,_84/* sjng */);
      }
    }
  }
},
_89/* getRadioValue2 */ = "(function (elId) { return $(elId); })",
_8a/* getRadioValue3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\']:checked"));
}),
_8b/* getRadioValue4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("[name=\'"));
}),
_8c/* getRadioValue_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.val(); })");
}),
_8d/* getRadioValue1 */ = function(_8e/* slMr */, _/* EXTERNAL */){
  var _8f/* slMC */ = eval/* EXTERNAL */(E(_89/* FormEngine.JQuery.getRadioValue2 */)),
  _8g/* slMK */ = __app1/* EXTERNAL */(E(_8f/* slMC */), toJSStr/* EXTERNAL */(B(_7/* GHC.Base.++ */(_8b/* FormEngine.JQuery.getRadioValue4 */, new T(function(){
    return B(_7/* GHC.Base.++ */(_8e/* slMr */, _8a/* FormEngine.JQuery.getRadioValue3 */));
  },1))))),
  _8h/* slMQ */ = __app1/* EXTERNAL */(E(_8c/* FormEngine.JQuery.getRadioValue_f1 */), _8g/* slMK */);
  return new T(function(){
    var _8i/* slMU */ = String/* EXTERNAL */(_8h/* slMQ */);
    return fromJSStr/* EXTERNAL */(_8i/* slMU */);
  });
},
_8j/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("undefined"));
}),
_8k/* nfiUnitId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_unit"));
}),
_8l/* readEither6 */ = function(_8m/*  s2Rf3 */){
  while(1){
    var _8n/*  readEither6 */ = B((function(_8o/* s2Rf3 */){
      var _8p/* s2Rf4 */ = E(_8o/* s2Rf3 */);
      if(!_8p/* s2Rf4 */._){
        return __Z/* EXTERNAL */;
      }else{
        var _8q/* s2Rf6 */ = _8p/* s2Rf4 */.b,
        _8r/* s2Rf7 */ = E(_8p/* s2Rf4 */.a);
        if(!E(_8r/* s2Rf7 */.b)._){
          return new T2(1,_8r/* s2Rf7 */.a,new T(function(){
            return B(_8l/* Text.Read.readEither6 */(_8q/* s2Rf6 */));
          }));
        }else{
          _8m/*  s2Rf3 */ = _8q/* s2Rf6 */;
          return __continue/* EXTERNAL */;
        }
      }
    })(_8m/*  s2Rf3 */));
    if(_8n/*  readEither6 */!=__continue/* EXTERNAL */){
      return _8n/*  readEither6 */;
    }
  }
},
_8s/* run */ = function(_8t/*  s1iAI */, _8u/*  s1iAJ */){
  while(1){
    var _8v/*  run */ = B((function(_8w/* s1iAI */, _8x/* s1iAJ */){
      var _8y/* s1iAK */ = E(_8w/* s1iAI */);
      switch(_8y/* s1iAK */._){
        case 0:
          var _8z/* s1iAM */ = E(_8x/* s1iAJ */);
          if(!_8z/* s1iAM */._){
            return __Z/* EXTERNAL */;
          }else{
            _8t/*  s1iAI */ = B(A1(_8y/* s1iAK */.a,_8z/* s1iAM */.a));
            _8u/*  s1iAJ */ = _8z/* s1iAM */.b;
            return __continue/* EXTERNAL */;
          }
          break;
        case 1:
          var _8A/*   s1iAI */ = B(A1(_8y/* s1iAK */.a,_8x/* s1iAJ */)),
          _8B/*   s1iAJ */ = _8x/* s1iAJ */;
          _8t/*  s1iAI */ = _8A/*   s1iAI */;
          _8u/*  s1iAJ */ = _8B/*   s1iAJ */;
          return __continue/* EXTERNAL */;
        case 2:
          return __Z/* EXTERNAL */;
        case 3:
          return new T2(1,new T2(0,_8y/* s1iAK */.a,_8x/* s1iAJ */),new T(function(){
            return B(_8s/* Text.ParserCombinators.ReadP.run */(_8y/* s1iAK */.b, _8x/* s1iAJ */));
          }));
        default:
          return E(_8y/* s1iAK */.a);
      }
    })(_8t/*  s1iAI */, _8u/*  s1iAJ */));
    if(_8v/*  run */!=__continue/* EXTERNAL */){
      return _8v/*  run */;
    }
  }
},
_8C/* selectByName2 */ = "(function (name) { return $(\'[name=\"\' + name + \'\"]\'); })",
_8D/* selectByName1 */ = function(_8E/* slJN */, _/* EXTERNAL */){
  var _8F/* slJX */ = eval/* EXTERNAL */(E(_8C/* FormEngine.JQuery.selectByName2 */));
  return new F(function(){return __app1/* EXTERNAL */(E(_8F/* slJX */), toJSStr/* EXTERNAL */(E(_8E/* slJN */)));});
},
_8G/* True */ = true,
_8H/* map */ = function(_8I/* s3ht */, _8J/* s3hu */){
  var _8K/* s3hv */ = E(_8J/* s3hu */);
  return (_8K/* s3hv */._==0) ? __Z/* EXTERNAL */ : new T2(1,new T(function(){
    return B(A1(_8I/* s3ht */,_8K/* s3hv */.a));
  }),new T(function(){
    return B(_8H/* GHC.Base.map */(_8I/* s3ht */, _8K/* s3hv */.b));
  }));
},
_8L/* $fExceptionNestedAtomically_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_8M/* $fExceptionNestedAtomically_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Control.Exception.Base"));
}),
_8N/* $fExceptionPatternMatchFail_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PatternMatchFail"));
}),
_8O/* $fExceptionPatternMatchFail_wild */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_8L/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_8M/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_8N/* Control.Exception.Base.$fExceptionPatternMatchFail_ww5 */),
_8P/* $fExceptionPatternMatchFail2 */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_8O/* Control.Exception.Base.$fExceptionPatternMatchFail_wild */,_k/* GHC.Types.[] */,_k/* GHC.Types.[] */),
_8Q/* $fExceptionPatternMatchFail1 */ = function(_8R/* s4nv1 */){
  return E(_8P/* Control.Exception.Base.$fExceptionPatternMatchFail2 */);
},
_8S/* $p1Exception */ = function(_8T/* s2Szo */){
  return E(E(_8T/* s2Szo */).a);
},
_8U/* cast */ = function(_8V/* s26is */, _8W/* s26it */, _8X/* s26iu */){
  var _8Y/* s26iv */ = B(A1(_8V/* s26is */,_/* EXTERNAL */)),
  _8Z/* s26iB */ = B(A1(_8W/* s26it */,_/* EXTERNAL */)),
  _90/* s26iI */ = hs_eqWord64/* EXTERNAL */(_8Y/* s26iv */.a, _8Z/* s26iB */.a);
  if(!_90/* s26iI */){
    return __Z/* EXTERNAL */;
  }else{
    var _91/* s26iN */ = hs_eqWord64/* EXTERNAL */(_8Y/* s26iv */.b, _8Z/* s26iB */.b);
    return (!_91/* s26iN */) ? __Z/* EXTERNAL */ : new T1(1,_8X/* s26iu */);
  }
},
_92/* $fExceptionPatternMatchFail_$cfromException */ = function(_93/* s4nvc */){
  var _94/* s4nvd */ = E(_93/* s4nvc */);
  return new F(function(){return _8U/* Data.Typeable.cast */(B(_8S/* GHC.Exception.$p1Exception */(_94/* s4nvd */.a)), _8Q/* Control.Exception.Base.$fExceptionPatternMatchFail1 */, _94/* s4nvd */.b);});
},
_95/* $fExceptionPatternMatchFail_$cshow */ = function(_96/* s4nv4 */){
  return E(E(_96/* s4nv4 */).a);
},
_97/* $fExceptionPatternMatchFail_$ctoException */ = function(_98/* B1 */){
  return new T2(0,_99/* Control.Exception.Base.$fExceptionPatternMatchFail */,_98/* B1 */);
},
_9a/* $fShowPatternMatchFail1 */ = function(_9b/* s4nqK */, _9c/* s4nqL */){
  return new F(function(){return _7/* GHC.Base.++ */(E(_9b/* s4nqK */).a, _9c/* s4nqL */);});
},
_9d/* $fShowPatternMatchFail_$cshowList */ = function(_9e/* s4nv2 */, _9f/* s4nv3 */){
  return new F(function(){return _5t/* GHC.Show.showList__ */(_9a/* Control.Exception.Base.$fShowPatternMatchFail1 */, _9e/* s4nv2 */, _9f/* s4nv3 */);});
},
_9g/* $fShowPatternMatchFail_$cshowsPrec */ = function(_9h/* s4nv7 */, _9i/* s4nv8 */, _9j/* s4nv9 */){
  return new F(function(){return _7/* GHC.Base.++ */(E(_9i/* s4nv8 */).a, _9j/* s4nv9 */);});
},
_9k/* $fShowPatternMatchFail */ = new T3(0,_9g/* Control.Exception.Base.$fShowPatternMatchFail_$cshowsPrec */,_95/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */,_9d/* Control.Exception.Base.$fShowPatternMatchFail_$cshowList */),
_99/* $fExceptionPatternMatchFail */ = new T(function(){
  return new T5(0,_8Q/* Control.Exception.Base.$fExceptionPatternMatchFail1 */,_9k/* Control.Exception.Base.$fShowPatternMatchFail */,_97/* Control.Exception.Base.$fExceptionPatternMatchFail_$ctoException */,_92/* Control.Exception.Base.$fExceptionPatternMatchFail_$cfromException */,_95/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */);
}),
_9l/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Non-exhaustive patterns in"));
}),
_9m/* toException */ = function(_9n/* s2SzC */){
  return E(E(_9n/* s2SzC */).c);
},
_9o/* lvl */ = function(_9p/* s2SzX */, _9q/* s2SzY */){
  return new F(function(){return die/* EXTERNAL */(new T(function(){
    return B(A2(_9m/* GHC.Exception.toException */,_9q/* s2SzY */, _9p/* s2SzX */));
  }));});
},
_9r/* throw1 */ = function(_9s/* B2 */, _9t/* B1 */){
  return new F(function(){return _9o/* GHC.Exception.lvl */(_9s/* B2 */, _9t/* B1 */);});
},
_9u/* $wspan */ = function(_9v/* s9vU */, _9w/* s9vV */){
  var _9x/* s9vW */ = E(_9w/* s9vV */);
  if(!_9x/* s9vW */._){
    return new T2(0,_k/* GHC.Types.[] */,_k/* GHC.Types.[] */);
  }else{
    var _9y/* s9vX */ = _9x/* s9vW */.a;
    if(!B(A1(_9v/* s9vU */,_9y/* s9vX */))){
      return new T2(0,_k/* GHC.Types.[] */,_9x/* s9vW */);
    }else{
      var _9z/* s9w0 */ = new T(function(){
        var _9A/* s9w1 */ = B(_9u/* GHC.List.$wspan */(_9v/* s9vU */, _9x/* s9vW */.b));
        return new T2(0,_9A/* s9w1 */.a,_9A/* s9w1 */.b);
      });
      return new T2(0,new T2(1,_9y/* s9vX */,new T(function(){
        return E(E(_9z/* s9w0 */).a);
      })),new T(function(){
        return E(E(_9z/* s9w0 */).b);
      }));
    }
  }
},
_9B/* untangle1 */ = 32,
_9C/* untangle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\n"));
}),
_9D/* untangle3 */ = function(_9E/* s3K4R */){
  return (E(_9E/* s3K4R */)==124) ? false : true;
},
_9F/* untangle */ = function(_9G/* s3K5K */, _9H/* s3K5L */){
  var _9I/* s3K5N */ = B(_9u/* GHC.List.$wspan */(_9D/* GHC.IO.Exception.untangle3 */, B(unCStr/* EXTERNAL */(_9G/* s3K5K */)))),
  _9J/* s3K5O */ = _9I/* s3K5N */.a,
  _9K/* s3K5Q */ = function(_9L/* s3K5R */, _9M/* s3K5S */){
    var _9N/* s3K5V */ = new T(function(){
      var _9O/* s3K5U */ = new T(function(){
        return B(_7/* GHC.Base.++ */(_9H/* s3K5L */, new T(function(){
          return B(_7/* GHC.Base.++ */(_9M/* s3K5S */, _9C/* GHC.IO.Exception.untangle2 */));
        },1)));
      });
      return B(unAppCStr/* EXTERNAL */(": ", _9O/* s3K5U */));
    },1);
    return new F(function(){return _7/* GHC.Base.++ */(_9L/* s3K5R */, _9N/* s3K5V */);});
  },
  _9P/* s3K5W */ = E(_9I/* s3K5N */.b);
  if(!_9P/* s3K5W */._){
    return new F(function(){return _9K/* s3K5Q */(_9J/* s3K5O */, _k/* GHC.Types.[] */);});
  }else{
    if(E(_9P/* s3K5W */.a)==124){
      return new F(function(){return _9K/* s3K5Q */(_9J/* s3K5O */, new T2(1,_9B/* GHC.IO.Exception.untangle1 */,_9P/* s3K5W */.b));});
    }else{
      return new F(function(){return _9K/* s3K5Q */(_9J/* s3K5O */, _k/* GHC.Types.[] */);});
    }
  }
},
_9Q/* patError */ = function(_9R/* s4nwI */){
  return new F(function(){return _9r/* GHC.Exception.throw1 */(new T1(0,new T(function(){
    return B(_9F/* GHC.IO.Exception.untangle */(_9R/* s4nwI */, _9l/* Control.Exception.Base.lvl3 */));
  })), _99/* Control.Exception.Base.$fExceptionPatternMatchFail */);});
},
_9S/* lvl2 */ = new T(function(){
  return B(_9Q/* Control.Exception.Base.patError */("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));
}),
_9T/* $fAlternativeP_$c<|> */ = function(_9U/* s1iBo */, _9V/* s1iBp */){
  var _9W/* s1iBq */ = function(_9X/* s1iBr */){
    var _9Y/* s1iBs */ = E(_9V/* s1iBp */);
    if(_9Y/* s1iBs */._==3){
      return new T2(3,_9Y/* s1iBs */.a,new T(function(){
        return B(_9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(_9U/* s1iBo */, _9Y/* s1iBs */.b));
      }));
    }else{
      var _9Z/* s1iBt */ = E(_9U/* s1iBo */);
      if(_9Z/* s1iBt */._==2){
        return E(_9Y/* s1iBs */);
      }else{
        var _a0/* s1iBu */ = E(_9Y/* s1iBs */);
        if(_a0/* s1iBu */._==2){
          return E(_9Z/* s1iBt */);
        }else{
          var _a1/* s1iBv */ = function(_a2/* s1iBw */){
            var _a3/* s1iBx */ = E(_a0/* s1iBu */);
            if(_a3/* s1iBx */._==4){
              var _a4/* s1iBU */ = function(_a5/* s1iBR */){
                return new T1(4,new T(function(){
                  return B(_7/* GHC.Base.++ */(B(_8s/* Text.ParserCombinators.ReadP.run */(_9Z/* s1iBt */, _a5/* s1iBR */)), _a3/* s1iBx */.a));
                }));
              };
              return new T1(1,_a4/* s1iBU */);
            }else{
              var _a6/* s1iBy */ = E(_9Z/* s1iBt */);
              if(_a6/* s1iBy */._==1){
                var _a7/* s1iBF */ = _a6/* s1iBy */.a,
                _a8/* s1iBG */ = E(_a3/* s1iBx */);
                if(!_a8/* s1iBG */._){
                  return new T1(1,function(_a9/* s1iBI */){
                    return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_a7/* s1iBF */,_a9/* s1iBI */)), _a8/* s1iBG */);});
                  });
                }else{
                  var _aa/* s1iBP */ = function(_ab/* s1iBM */){
                    return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_a7/* s1iBF */,_ab/* s1iBM */)), new T(function(){
                      return B(A1(_a8/* s1iBG */.a,_ab/* s1iBM */));
                    }));});
                  };
                  return new T1(1,_aa/* s1iBP */);
                }
              }else{
                var _ac/* s1iBz */ = E(_a3/* s1iBx */);
                if(!_ac/* s1iBz */._){
                  return E(_9S/* Text.ParserCombinators.ReadP.lvl2 */);
                }else{
                  var _ad/* s1iBE */ = function(_ae/* s1iBC */){
                    return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(_a6/* s1iBy */, new T(function(){
                      return B(A1(_ac/* s1iBz */.a,_ae/* s1iBC */));
                    }));});
                  };
                  return new T1(1,_ad/* s1iBE */);
                }
              }
            }
          },
          _af/* s1iBV */ = E(_9Z/* s1iBt */);
          switch(_af/* s1iBV */._){
            case 1:
              var _ag/* s1iBX */ = E(_a0/* s1iBu */);
              if(_ag/* s1iBX */._==4){
                var _ah/* s1iC3 */ = function(_ai/* s1iBZ */){
                  return new T1(4,new T(function(){
                    return B(_7/* GHC.Base.++ */(B(_8s/* Text.ParserCombinators.ReadP.run */(B(A1(_af/* s1iBV */.a,_ai/* s1iBZ */)), _ai/* s1iBZ */)), _ag/* s1iBX */.a));
                  }));
                };
                return new T1(1,_ah/* s1iC3 */);
              }else{
                return new F(function(){return _a1/* s1iBv */(_/* EXTERNAL */);});
              }
              break;
            case 4:
              var _aj/* s1iC4 */ = _af/* s1iBV */.a,
              _ak/* s1iC5 */ = E(_a0/* s1iBu */);
              switch(_ak/* s1iC5 */._){
                case 0:
                  var _al/* s1iCa */ = function(_am/* s1iC7 */){
                    var _an/* s1iC9 */ = new T(function(){
                      return B(_7/* GHC.Base.++ */(_aj/* s1iC4 */, new T(function(){
                        return B(_8s/* Text.ParserCombinators.ReadP.run */(_ak/* s1iC5 */, _am/* s1iC7 */));
                      },1)));
                    });
                    return new T1(4,_an/* s1iC9 */);
                  };
                  return new T1(1,_al/* s1iCa */);
                case 1:
                  var _ao/* s1iCg */ = function(_ap/* s1iCc */){
                    var _aq/* s1iCf */ = new T(function(){
                      return B(_7/* GHC.Base.++ */(_aj/* s1iC4 */, new T(function(){
                        return B(_8s/* Text.ParserCombinators.ReadP.run */(B(A1(_ak/* s1iC5 */.a,_ap/* s1iCc */)), _ap/* s1iCc */));
                      },1)));
                    });
                    return new T1(4,_aq/* s1iCf */);
                  };
                  return new T1(1,_ao/* s1iCg */);
                default:
                  return new T1(4,new T(function(){
                    return B(_7/* GHC.Base.++ */(_aj/* s1iC4 */, _ak/* s1iC5 */.a));
                  }));
              }
              break;
            default:
              return new F(function(){return _a1/* s1iBv */(_/* EXTERNAL */);});
          }
        }
      }
    }
  },
  _ar/* s1iCm */ = E(_9U/* s1iBo */);
  switch(_ar/* s1iCm */._){
    case 0:
      var _as/* s1iCo */ = E(_9V/* s1iBp */);
      if(!_as/* s1iCo */._){
        var _at/* s1iCt */ = function(_au/* s1iCq */){
          return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_ar/* s1iCm */.a,_au/* s1iCq */)), new T(function(){
            return B(A1(_as/* s1iCo */.a,_au/* s1iCq */));
          }));});
        };
        return new T1(0,_at/* s1iCt */);
      }else{
        return new F(function(){return _9W/* s1iBq */(_/* EXTERNAL */);});
      }
      break;
    case 3:
      return new T2(3,_ar/* s1iCm */.a,new T(function(){
        return B(_9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(_ar/* s1iCm */.b, _9V/* s1iBp */));
      }));
    default:
      return new F(function(){return _9W/* s1iBq */(_/* EXTERNAL */);});
  }
},
_av/* $fRead(,)3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("("));
}),
_aw/* $fRead(,)4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_ax/* $fEqChar_$c/= */ = function(_ay/* scFn */, _az/* scFo */){
  return E(_ay/* scFn */)!=E(_az/* scFo */);
},
_aA/* $fEqChar_$c== */ = function(_aB/* scFu */, _aC/* scFv */){
  return E(_aB/* scFu */)==E(_aC/* scFv */);
},
_aD/* $fEqChar */ = new T2(0,_aA/* GHC.Classes.$fEqChar_$c== */,_ax/* GHC.Classes.$fEqChar_$c/= */),
_aE/* $fEq[]_$s$c==1 */ = function(_aF/* scIY */, _aG/* scIZ */){
  while(1){
    var _aH/* scJ0 */ = E(_aF/* scIY */);
    if(!_aH/* scJ0 */._){
      return (E(_aG/* scIZ */)._==0) ? true : false;
    }else{
      var _aI/* scJ6 */ = E(_aG/* scIZ */);
      if(!_aI/* scJ6 */._){
        return false;
      }else{
        if(E(_aH/* scJ0 */.a)!=E(_aI/* scJ6 */.a)){
          return false;
        }else{
          _aF/* scIY */ = _aH/* scJ0 */.b;
          _aG/* scIZ */ = _aI/* scJ6 */.b;
          continue;
        }
      }
    }
  }
},
_aJ/* $fEq[]_$s$c/=1 */ = function(_aK/* scJE */, _aL/* scJF */){
  return (!B(_aE/* GHC.Classes.$fEq[]_$s$c==1 */(_aK/* scJE */, _aL/* scJF */))) ? true : false;
},
_aM/* $fEq[]_$s$fEq[]1 */ = new T2(0,_aE/* GHC.Classes.$fEq[]_$s$c==1 */,_aJ/* GHC.Classes.$fEq[]_$s$c/=1 */),
_aN/* $fAlternativeP_$c>>= */ = function(_aO/* s1iCx */, _aP/* s1iCy */){
  var _aQ/* s1iCz */ = E(_aO/* s1iCx */);
  switch(_aQ/* s1iCz */._){
    case 0:
      return new T1(0,function(_aR/* s1iCB */){
        return new F(function(){return _aN/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(B(A1(_aQ/* s1iCz */.a,_aR/* s1iCB */)), _aP/* s1iCy */);});
      });
    case 1:
      return new T1(1,function(_aS/* s1iCF */){
        return new F(function(){return _aN/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(B(A1(_aQ/* s1iCz */.a,_aS/* s1iCF */)), _aP/* s1iCy */);});
      });
    case 2:
      return new T0(2);
    case 3:
      return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_aP/* s1iCy */,_aQ/* s1iCz */.a)), new T(function(){
        return B(_aN/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(_aQ/* s1iCz */.b, _aP/* s1iCy */));
      }));});
      break;
    default:
      var _aT/* s1iCN */ = function(_aU/* s1iCO */){
        var _aV/* s1iCP */ = E(_aU/* s1iCO */);
        if(!_aV/* s1iCP */._){
          return __Z/* EXTERNAL */;
        }else{
          var _aW/* s1iCS */ = E(_aV/* s1iCP */.a);
          return new F(function(){return _7/* GHC.Base.++ */(B(_8s/* Text.ParserCombinators.ReadP.run */(B(A1(_aP/* s1iCy */,_aW/* s1iCS */.a)), _aW/* s1iCS */.b)), new T(function(){
            return B(_aT/* s1iCN */(_aV/* s1iCP */.b));
          },1));});
        }
      },
      _aX/* s1iCY */ = B(_aT/* s1iCN */(_aQ/* s1iCz */.a));
      return (_aX/* s1iCY */._==0) ? new T0(2) : new T1(4,_aX/* s1iCY */);
  }
},
_aY/* Fail */ = new T0(2),
_aZ/* $fApplicativeP_$creturn */ = function(_b0/* s1iBl */){
  return new T2(3,_b0/* s1iBl */,_aY/* Text.ParserCombinators.ReadP.Fail */);
},
_b1/* <++2 */ = function(_b2/* s1iyp */, _b3/* s1iyq */){
  var _b4/* s1iyr */ = E(_b2/* s1iyp */);
  if(!_b4/* s1iyr */){
    return new F(function(){return A1(_b3/* s1iyq */,_0/* GHC.Tuple.() */);});
  }else{
    var _b5/* s1iys */ = new T(function(){
      return B(_b1/* Text.ParserCombinators.ReadP.<++2 */(_b4/* s1iyr */-1|0, _b3/* s1iyq */));
    });
    return new T1(0,function(_b6/* s1iyu */){
      return E(_b5/* s1iys */);
    });
  }
},
_b7/* $wa */ = function(_b8/* s1iD8 */, _b9/* s1iD9 */, _ba/* s1iDa */){
  var _bb/* s1iDb */ = new T(function(){
    return B(A1(_b8/* s1iD8 */,_aZ/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
  }),
  _bc/* s1iDc */ = function(_bd/*  s1iDd */, _be/*  s1iDe */, _bf/*  s1iDf */, _bg/*  s1iDg */){
    while(1){
      var _bh/*  s1iDc */ = B((function(_bi/* s1iDd */, _bj/* s1iDe */, _bk/* s1iDf */, _bl/* s1iDg */){
        var _bm/* s1iDh */ = E(_bi/* s1iDd */);
        switch(_bm/* s1iDh */._){
          case 0:
            var _bn/* s1iDj */ = E(_bj/* s1iDe */);
            if(!_bn/* s1iDj */._){
              return new F(function(){return A1(_b9/* s1iD9 */,_bl/* s1iDg */);});
            }else{
              var _bo/*   s1iDf */ = _bk/* s1iDf */+1|0,
              _bp/*   s1iDg */ = _bl/* s1iDg */;
              _bd/*  s1iDd */ = B(A1(_bm/* s1iDh */.a,_bn/* s1iDj */.a));
              _be/*  s1iDe */ = _bn/* s1iDj */.b;
              _bf/*  s1iDf */ = _bo/*   s1iDf */;
              _bg/*  s1iDg */ = _bp/*   s1iDg */;
              return __continue/* EXTERNAL */;
            }
            break;
          case 1:
            var _bq/*   s1iDd */ = B(A1(_bm/* s1iDh */.a,_bj/* s1iDe */)),
            _br/*   s1iDe */ = _bj/* s1iDe */,
            _bo/*   s1iDf */ = _bk/* s1iDf */,
            _bp/*   s1iDg */ = _bl/* s1iDg */;
            _bd/*  s1iDd */ = _bq/*   s1iDd */;
            _be/*  s1iDe */ = _br/*   s1iDe */;
            _bf/*  s1iDf */ = _bo/*   s1iDf */;
            _bg/*  s1iDg */ = _bp/*   s1iDg */;
            return __continue/* EXTERNAL */;
          case 2:
            return new F(function(){return A1(_b9/* s1iD9 */,_bl/* s1iDg */);});
            break;
          case 3:
            var _bs/* s1iDs */ = new T(function(){
              return B(_aN/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(_bm/* s1iDh */, _bl/* s1iDg */));
            });
            return new F(function(){return _b1/* Text.ParserCombinators.ReadP.<++2 */(_bk/* s1iDf */, function(_bt/* s1iDt */){
              return E(_bs/* s1iDs */);
            });});
            break;
          default:
            return new F(function(){return _aN/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(_bm/* s1iDh */, _bl/* s1iDg */);});
        }
      })(_bd/*  s1iDd */, _be/*  s1iDe */, _bf/*  s1iDf */, _bg/*  s1iDg */));
      if(_bh/*  s1iDc */!=__continue/* EXTERNAL */){
        return _bh/*  s1iDc */;
      }
    }
  };
  return function(_bu/* s1iDw */){
    return new F(function(){return _bc/* s1iDc */(_bb/* s1iDb */, _bu/* s1iDw */, 0, _ba/* s1iDa */);});
  };
},
_bv/* munch3 */ = function(_bw/* s1iyo */){
  return new F(function(){return A1(_bw/* s1iyo */,_k/* GHC.Types.[] */);});
},
_bx/* $wa3 */ = function(_by/* s1iyQ */, _bz/* s1iyR */){
  var _bA/* s1iyS */ = function(_bB/* s1iyT */){
    var _bC/* s1iyU */ = E(_bB/* s1iyT */);
    if(!_bC/* s1iyU */._){
      return E(_bv/* Text.ParserCombinators.ReadP.munch3 */);
    }else{
      var _bD/* s1iyV */ = _bC/* s1iyU */.a;
      if(!B(A1(_by/* s1iyQ */,_bD/* s1iyV */))){
        return E(_bv/* Text.ParserCombinators.ReadP.munch3 */);
      }else{
        var _bE/* s1iyY */ = new T(function(){
          return B(_bA/* s1iyS */(_bC/* s1iyU */.b));
        }),
        _bF/* s1iz6 */ = function(_bG/* s1iyZ */){
          var _bH/* s1iz0 */ = new T(function(){
            return B(A1(_bE/* s1iyY */,function(_bI/* s1iz1 */){
              return new F(function(){return A1(_bG/* s1iyZ */,new T2(1,_bD/* s1iyV */,_bI/* s1iz1 */));});
            }));
          });
          return new T1(0,function(_bJ/* s1iz4 */){
            return E(_bH/* s1iz0 */);
          });
        };
        return E(_bF/* s1iz6 */);
      }
    }
  };
  return function(_bK/* s1iz7 */){
    return new F(function(){return A2(_bA/* s1iyS */,_bK/* s1iz7 */, _bz/* s1iyR */);});
  };
},
_bL/* EOF */ = new T0(6),
_bM/* id */ = function(_bN/* s3aI */){
  return E(_bN/* s3aI */);
},
_bO/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("valDig: Bad base"));
}),
_bP/* readDecP2 */ = new T(function(){
  return B(err/* EXTERNAL */(_bO/* Text.Read.Lex.lvl37 */));
}),
_bQ/* $wa6 */ = function(_bR/* s1oaO */, _bS/* s1oaP */){
  var _bT/* s1oaQ */ = function(_bU/* s1oaR */, _bV/* s1oaS */){
    var _bW/* s1oaT */ = E(_bU/* s1oaR */);
    if(!_bW/* s1oaT */._){
      var _bX/* s1oaU */ = new T(function(){
        return B(A1(_bV/* s1oaS */,_k/* GHC.Types.[] */));
      });
      return function(_bY/* s1oaV */){
        return new F(function(){return A1(_bY/* s1oaV */,_bX/* s1oaU */);});
      };
    }else{
      var _bZ/* s1ob1 */ = E(_bW/* s1oaT */.a),
      _c0/* s1ob3 */ = function(_c1/* s1ob4 */){
        var _c2/* s1ob5 */ = new T(function(){
          return B(_bT/* s1oaQ */(_bW/* s1oaT */.b, function(_c3/* s1ob6 */){
            return new F(function(){return A1(_bV/* s1oaS */,new T2(1,_c1/* s1ob4 */,_c3/* s1ob6 */));});
          }));
        }),
        _c4/* s1obd */ = function(_c5/* s1ob9 */){
          var _c6/* s1oba */ = new T(function(){
            return B(A1(_c2/* s1ob5 */,_c5/* s1ob9 */));
          });
          return new T1(0,function(_c7/* s1obb */){
            return E(_c6/* s1oba */);
          });
        };
        return E(_c4/* s1obd */);
      };
      switch(E(_bR/* s1oaO */)){
        case 8:
          if(48>_bZ/* s1ob1 */){
            var _c8/* s1obi */ = new T(function(){
              return B(A1(_bV/* s1oaS */,_k/* GHC.Types.[] */));
            });
            return function(_c9/* s1obj */){
              return new F(function(){return A1(_c9/* s1obj */,_c8/* s1obi */);});
            };
          }else{
            if(_bZ/* s1ob1 */>55){
              var _ca/* s1obn */ = new T(function(){
                return B(A1(_bV/* s1oaS */,_k/* GHC.Types.[] */));
              });
              return function(_cb/* s1obo */){
                return new F(function(){return A1(_cb/* s1obo */,_ca/* s1obn */);});
              };
            }else{
              return new F(function(){return _c0/* s1ob3 */(_bZ/* s1ob1 */-48|0);});
            }
          }
          break;
        case 10:
          if(48>_bZ/* s1ob1 */){
            var _cc/* s1obv */ = new T(function(){
              return B(A1(_bV/* s1oaS */,_k/* GHC.Types.[] */));
            });
            return function(_cd/* s1obw */){
              return new F(function(){return A1(_cd/* s1obw */,_cc/* s1obv */);});
            };
          }else{
            if(_bZ/* s1ob1 */>57){
              var _ce/* s1obA */ = new T(function(){
                return B(A1(_bV/* s1oaS */,_k/* GHC.Types.[] */));
              });
              return function(_cf/* s1obB */){
                return new F(function(){return A1(_cf/* s1obB */,_ce/* s1obA */);});
              };
            }else{
              return new F(function(){return _c0/* s1ob3 */(_bZ/* s1ob1 */-48|0);});
            }
          }
          break;
        case 16:
          if(48>_bZ/* s1ob1 */){
            if(97>_bZ/* s1ob1 */){
              if(65>_bZ/* s1ob1 */){
                var _cg/* s1obM */ = new T(function(){
                  return B(A1(_bV/* s1oaS */,_k/* GHC.Types.[] */));
                });
                return function(_ch/* s1obN */){
                  return new F(function(){return A1(_ch/* s1obN */,_cg/* s1obM */);});
                };
              }else{
                if(_bZ/* s1ob1 */>70){
                  var _ci/* s1obR */ = new T(function(){
                    return B(A1(_bV/* s1oaS */,_k/* GHC.Types.[] */));
                  });
                  return function(_cj/* s1obS */){
                    return new F(function(){return A1(_cj/* s1obS */,_ci/* s1obR */);});
                  };
                }else{
                  return new F(function(){return _c0/* s1ob3 */((_bZ/* s1ob1 */-65|0)+10|0);});
                }
              }
            }else{
              if(_bZ/* s1ob1 */>102){
                if(65>_bZ/* s1ob1 */){
                  var _ck/* s1oc2 */ = new T(function(){
                    return B(A1(_bV/* s1oaS */,_k/* GHC.Types.[] */));
                  });
                  return function(_cl/* s1oc3 */){
                    return new F(function(){return A1(_cl/* s1oc3 */,_ck/* s1oc2 */);});
                  };
                }else{
                  if(_bZ/* s1ob1 */>70){
                    var _cm/* s1oc7 */ = new T(function(){
                      return B(A1(_bV/* s1oaS */,_k/* GHC.Types.[] */));
                    });
                    return function(_cn/* s1oc8 */){
                      return new F(function(){return A1(_cn/* s1oc8 */,_cm/* s1oc7 */);});
                    };
                  }else{
                    return new F(function(){return _c0/* s1ob3 */((_bZ/* s1ob1 */-65|0)+10|0);});
                  }
                }
              }else{
                return new F(function(){return _c0/* s1ob3 */((_bZ/* s1ob1 */-97|0)+10|0);});
              }
            }
          }else{
            if(_bZ/* s1ob1 */>57){
              if(97>_bZ/* s1ob1 */){
                if(65>_bZ/* s1ob1 */){
                  var _co/* s1oco */ = new T(function(){
                    return B(A1(_bV/* s1oaS */,_k/* GHC.Types.[] */));
                  });
                  return function(_cp/* s1ocp */){
                    return new F(function(){return A1(_cp/* s1ocp */,_co/* s1oco */);});
                  };
                }else{
                  if(_bZ/* s1ob1 */>70){
                    var _cq/* s1oct */ = new T(function(){
                      return B(A1(_bV/* s1oaS */,_k/* GHC.Types.[] */));
                    });
                    return function(_cr/* s1ocu */){
                      return new F(function(){return A1(_cr/* s1ocu */,_cq/* s1oct */);});
                    };
                  }else{
                    return new F(function(){return _c0/* s1ob3 */((_bZ/* s1ob1 */-65|0)+10|0);});
                  }
                }
              }else{
                if(_bZ/* s1ob1 */>102){
                  if(65>_bZ/* s1ob1 */){
                    var _cs/* s1ocE */ = new T(function(){
                      return B(A1(_bV/* s1oaS */,_k/* GHC.Types.[] */));
                    });
                    return function(_ct/* s1ocF */){
                      return new F(function(){return A1(_ct/* s1ocF */,_cs/* s1ocE */);});
                    };
                  }else{
                    if(_bZ/* s1ob1 */>70){
                      var _cu/* s1ocJ */ = new T(function(){
                        return B(A1(_bV/* s1oaS */,_k/* GHC.Types.[] */));
                      });
                      return function(_cv/* s1ocK */){
                        return new F(function(){return A1(_cv/* s1ocK */,_cu/* s1ocJ */);});
                      };
                    }else{
                      return new F(function(){return _c0/* s1ob3 */((_bZ/* s1ob1 */-65|0)+10|0);});
                    }
                  }
                }else{
                  return new F(function(){return _c0/* s1ob3 */((_bZ/* s1ob1 */-97|0)+10|0);});
                }
              }
            }else{
              return new F(function(){return _c0/* s1ob3 */(_bZ/* s1ob1 */-48|0);});
            }
          }
          break;
        default:
          return E(_bP/* Text.Read.Lex.readDecP2 */);
      }
    }
  },
  _cw/* s1ocX */ = function(_cx/* s1ocY */){
    var _cy/* s1ocZ */ = E(_cx/* s1ocY */);
    if(!_cy/* s1ocZ */._){
      return new T0(2);
    }else{
      return new F(function(){return A1(_bS/* s1oaP */,_cy/* s1ocZ */);});
    }
  };
  return function(_cz/* s1od2 */){
    return new F(function(){return A3(_bT/* s1oaQ */,_cz/* s1od2 */, _bM/* GHC.Base.id */, _cw/* s1ocX */);});
  };
},
_cA/* lvl41 */ = 16,
_cB/* lvl42 */ = 8,
_cC/* $wa7 */ = function(_cD/* s1od4 */){
  var _cE/* s1od5 */ = function(_cF/* s1od6 */){
    return new F(function(){return A1(_cD/* s1od4 */,new T1(5,new T2(0,_cB/* Text.Read.Lex.lvl42 */,_cF/* s1od6 */)));});
  },
  _cG/* s1od9 */ = function(_cH/* s1oda */){
    return new F(function(){return A1(_cD/* s1od4 */,new T1(5,new T2(0,_cA/* Text.Read.Lex.lvl41 */,_cH/* s1oda */)));});
  },
  _cI/* s1odd */ = function(_cJ/* s1ode */){
    switch(E(_cJ/* s1ode */)){
      case 79:
        return new T1(1,B(_bQ/* Text.Read.Lex.$wa6 */(_cB/* Text.Read.Lex.lvl42 */, _cE/* s1od5 */)));
      case 88:
        return new T1(1,B(_bQ/* Text.Read.Lex.$wa6 */(_cA/* Text.Read.Lex.lvl41 */, _cG/* s1od9 */)));
      case 111:
        return new T1(1,B(_bQ/* Text.Read.Lex.$wa6 */(_cB/* Text.Read.Lex.lvl42 */, _cE/* s1od5 */)));
      case 120:
        return new T1(1,B(_bQ/* Text.Read.Lex.$wa6 */(_cA/* Text.Read.Lex.lvl41 */, _cG/* s1od9 */)));
      default:
        return new T0(2);
    }
  };
  return function(_cK/* s1odr */){
    return (E(_cK/* s1odr */)==48) ? E(new T1(0,_cI/* s1odd */)) : new T0(2);
  };
},
_cL/* a2 */ = function(_cM/* s1odw */){
  return new T1(0,B(_cC/* Text.Read.Lex.$wa7 */(_cM/* s1odw */)));
},
_cN/* a */ = function(_cO/* s1o94 */){
  return new F(function(){return A1(_cO/* s1o94 */,_4y/* GHC.Base.Nothing */);});
},
_cP/* a1 */ = function(_cQ/* s1o95 */){
  return new F(function(){return A1(_cQ/* s1o95 */,_4y/* GHC.Base.Nothing */);});
},
_cR/* lvl */ = 10,
_cS/* log2I1 */ = new T1(0,1),
_cT/* lvl2 */ = new T1(0,2147483647),
_cU/* plusInteger */ = function(_cV/* s1Qe */, _cW/* s1Qf */){
  while(1){
    var _cX/* s1Qg */ = E(_cV/* s1Qe */);
    if(!_cX/* s1Qg */._){
      var _cY/* s1Qh */ = _cX/* s1Qg */.a,
      _cZ/* s1Qi */ = E(_cW/* s1Qf */);
      if(!_cZ/* s1Qi */._){
        var _d0/* s1Qj */ = _cZ/* s1Qi */.a,
        _d1/* s1Qk */ = addC/* EXTERNAL */(_cY/* s1Qh */, _d0/* s1Qj */);
        if(!E(_d1/* s1Qk */.b)){
          return new T1(0,_d1/* s1Qk */.a);
        }else{
          _cV/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_cY/* s1Qh */));
          _cW/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_d0/* s1Qj */));
          continue;
        }
      }else{
        _cV/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_cY/* s1Qh */));
        _cW/* s1Qf */ = _cZ/* s1Qi */;
        continue;
      }
    }else{
      var _d2/* s1Qz */ = E(_cW/* s1Qf */);
      if(!_d2/* s1Qz */._){
        _cV/* s1Qe */ = _cX/* s1Qg */;
        _cW/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_d2/* s1Qz */.a));
        continue;
      }else{
        return new T1(1,I_add/* EXTERNAL */(_cX/* s1Qg */.a, _d2/* s1Qz */.a));
      }
    }
  }
},
_d3/* lvl3 */ = new T(function(){
  return B(_cU/* GHC.Integer.Type.plusInteger */(_cT/* GHC.Integer.Type.lvl2 */, _cS/* GHC.Integer.Type.log2I1 */));
}),
_d4/* negateInteger */ = function(_d5/* s1QH */){
  var _d6/* s1QI */ = E(_d5/* s1QH */);
  if(!_d6/* s1QI */._){
    var _d7/* s1QK */ = E(_d6/* s1QI */.a);
    return (_d7/* s1QK */==(-2147483648)) ? E(_d3/* GHC.Integer.Type.lvl3 */) : new T1(0, -_d7/* s1QK */);
  }else{
    return new T1(1,I_negate/* EXTERNAL */(_d6/* s1QI */.a));
  }
},
_d8/* numberToFixed1 */ = new T1(0,10),
_d9/* $wlenAcc */ = function(_da/* s9Bd */, _db/* s9Be */){
  while(1){
    var _dc/* s9Bf */ = E(_da/* s9Bd */);
    if(!_dc/* s9Bf */._){
      return E(_db/* s9Be */);
    }else{
      var _dd/*  s9Be */ = _db/* s9Be */+1|0;
      _da/* s9Bd */ = _dc/* s9Bf */.b;
      _db/* s9Be */ = _dd/*  s9Be */;
      continue;
    }
  }
},
_de/* smallInteger */ = function(_df/* B1 */){
  return new T1(0,_df/* B1 */);
},
_dg/* numberToFixed2 */ = function(_dh/* s1o9e */){
  return new F(function(){return _de/* GHC.Integer.Type.smallInteger */(E(_dh/* s1o9e */));});
},
_di/* lvl39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("this should not happen"));
}),
_dj/* lvl40 */ = new T(function(){
  return B(err/* EXTERNAL */(_di/* Text.Read.Lex.lvl39 */));
}),
_dk/* timesInteger */ = function(_dl/* s1PN */, _dm/* s1PO */){
  while(1){
    var _dn/* s1PP */ = E(_dl/* s1PN */);
    if(!_dn/* s1PP */._){
      var _do/* s1PQ */ = _dn/* s1PP */.a,
      _dp/* s1PR */ = E(_dm/* s1PO */);
      if(!_dp/* s1PR */._){
        var _dq/* s1PS */ = _dp/* s1PR */.a;
        if(!(imul/* EXTERNAL */(_do/* s1PQ */, _dq/* s1PS */)|0)){
          return new T1(0,imul/* EXTERNAL */(_do/* s1PQ */, _dq/* s1PS */)|0);
        }else{
          _dl/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_do/* s1PQ */));
          _dm/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_dq/* s1PS */));
          continue;
        }
      }else{
        _dl/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_do/* s1PQ */));
        _dm/* s1PO */ = _dp/* s1PR */;
        continue;
      }
    }else{
      var _dr/* s1Q6 */ = E(_dm/* s1PO */);
      if(!_dr/* s1Q6 */._){
        _dl/* s1PN */ = _dn/* s1PP */;
        _dm/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_dr/* s1Q6 */.a));
        continue;
      }else{
        return new T1(1,I_mul/* EXTERNAL */(_dn/* s1PP */.a, _dr/* s1Q6 */.a));
      }
    }
  }
},
_ds/* combine */ = function(_dt/* s1o9h */, _du/* s1o9i */){
  var _dv/* s1o9j */ = E(_du/* s1o9i */);
  if(!_dv/* s1o9j */._){
    return __Z/* EXTERNAL */;
  }else{
    var _dw/* s1o9m */ = E(_dv/* s1o9j */.b);
    return (_dw/* s1o9m */._==0) ? E(_dj/* Text.Read.Lex.lvl40 */) : new T2(1,B(_cU/* GHC.Integer.Type.plusInteger */(B(_dk/* GHC.Integer.Type.timesInteger */(_dv/* s1o9j */.a, _dt/* s1o9h */)), _dw/* s1o9m */.a)),new T(function(){
      return B(_ds/* Text.Read.Lex.combine */(_dt/* s1o9h */, _dw/* s1o9m */.b));
    }));
  }
},
_dx/* numberToFixed3 */ = new T1(0,0),
_dy/* numberToFixed_go */ = function(_dz/*  s1o9s */, _dA/*  s1o9t */, _dB/*  s1o9u */){
  while(1){
    var _dC/*  numberToFixed_go */ = B((function(_dD/* s1o9s */, _dE/* s1o9t */, _dF/* s1o9u */){
      var _dG/* s1o9v */ = E(_dF/* s1o9u */);
      if(!_dG/* s1o9v */._){
        return E(_dx/* Text.Read.Lex.numberToFixed3 */);
      }else{
        if(!E(_dG/* s1o9v */.b)._){
          return E(_dG/* s1o9v */.a);
        }else{
          var _dH/* s1o9B */ = E(_dE/* s1o9t */);
          if(_dH/* s1o9B */<=40){
            var _dI/* s1o9F */ = function(_dJ/* s1o9G */, _dK/* s1o9H */){
              while(1){
                var _dL/* s1o9I */ = E(_dK/* s1o9H */);
                if(!_dL/* s1o9I */._){
                  return E(_dJ/* s1o9G */);
                }else{
                  var _dM/*  s1o9G */ = B(_cU/* GHC.Integer.Type.plusInteger */(B(_dk/* GHC.Integer.Type.timesInteger */(_dJ/* s1o9G */, _dD/* s1o9s */)), _dL/* s1o9I */.a));
                  _dJ/* s1o9G */ = _dM/*  s1o9G */;
                  _dK/* s1o9H */ = _dL/* s1o9I */.b;
                  continue;
                }
              }
            };
            return new F(function(){return _dI/* s1o9F */(_dx/* Text.Read.Lex.numberToFixed3 */, _dG/* s1o9v */);});
          }else{
            var _dN/* s1o9N */ = B(_dk/* GHC.Integer.Type.timesInteger */(_dD/* s1o9s */, _dD/* s1o9s */));
            if(!(_dH/* s1o9B */%2)){
              var _dO/*   s1o9u */ = B(_ds/* Text.Read.Lex.combine */(_dD/* s1o9s */, _dG/* s1o9v */));
              _dz/*  s1o9s */ = _dN/* s1o9N */;
              _dA/*  s1o9t */ = quot/* EXTERNAL */(_dH/* s1o9B */+1|0, 2);
              _dB/*  s1o9u */ = _dO/*   s1o9u */;
              return __continue/* EXTERNAL */;
            }else{
              var _dO/*   s1o9u */ = B(_ds/* Text.Read.Lex.combine */(_dD/* s1o9s */, new T2(1,_dx/* Text.Read.Lex.numberToFixed3 */,_dG/* s1o9v */)));
              _dz/*  s1o9s */ = _dN/* s1o9N */;
              _dA/*  s1o9t */ = quot/* EXTERNAL */(_dH/* s1o9B */+1|0, 2);
              _dB/*  s1o9u */ = _dO/*   s1o9u */;
              return __continue/* EXTERNAL */;
            }
          }
        }
      }
    })(_dz/*  s1o9s */, _dA/*  s1o9t */, _dB/*  s1o9u */));
    if(_dC/*  numberToFixed_go */!=__continue/* EXTERNAL */){
      return _dC/*  numberToFixed_go */;
    }
  }
},
_dP/* valInteger */ = function(_dQ/* s1off */, _dR/* s1ofg */){
  return new F(function(){return _dy/* Text.Read.Lex.numberToFixed_go */(_dQ/* s1off */, new T(function(){
    return B(_d9/* GHC.List.$wlenAcc */(_dR/* s1ofg */, 0));
  },1), B(_8H/* GHC.Base.map */(_dg/* Text.Read.Lex.numberToFixed2 */, _dR/* s1ofg */)));});
},
_dS/* a26 */ = function(_dT/* s1og4 */){
  var _dU/* s1og5 */ = new T(function(){
    var _dV/* s1ogC */ = new T(function(){
      var _dW/* s1ogz */ = function(_dX/* s1ogw */){
        return new F(function(){return A1(_dT/* s1og4 */,new T1(1,new T(function(){
          return B(_dP/* Text.Read.Lex.valInteger */(_d8/* Text.Read.Lex.numberToFixed1 */, _dX/* s1ogw */));
        })));});
      };
      return new T1(1,B(_bQ/* Text.Read.Lex.$wa6 */(_cR/* Text.Read.Lex.lvl */, _dW/* s1ogz */)));
    }),
    _dY/* s1ogt */ = function(_dZ/* s1ogj */){
      if(E(_dZ/* s1ogj */)==43){
        var _e0/* s1ogq */ = function(_e1/* s1ogn */){
          return new F(function(){return A1(_dT/* s1og4 */,new T1(1,new T(function(){
            return B(_dP/* Text.Read.Lex.valInteger */(_d8/* Text.Read.Lex.numberToFixed1 */, _e1/* s1ogn */));
          })));});
        };
        return new T1(1,B(_bQ/* Text.Read.Lex.$wa6 */(_cR/* Text.Read.Lex.lvl */, _e0/* s1ogq */)));
      }else{
        return new T0(2);
      }
    },
    _e2/* s1ogh */ = function(_e3/* s1og6 */){
      if(E(_e3/* s1og6 */)==45){
        var _e4/* s1oge */ = function(_e5/* s1oga */){
          return new F(function(){return A1(_dT/* s1og4 */,new T1(1,new T(function(){
            return B(_d4/* GHC.Integer.Type.negateInteger */(B(_dP/* Text.Read.Lex.valInteger */(_d8/* Text.Read.Lex.numberToFixed1 */, _e5/* s1oga */))));
          })));});
        };
        return new T1(1,B(_bQ/* Text.Read.Lex.$wa6 */(_cR/* Text.Read.Lex.lvl */, _e4/* s1oge */)));
      }else{
        return new T0(2);
      }
    };
    return B(_9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(_9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,_e2/* s1ogh */), new T1(0,_dY/* s1ogt */))), _dV/* s1ogC */));
  });
  return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_e6/* s1ogD */){
    return (E(_e6/* s1ogD */)==101) ? E(_dU/* s1og5 */) : new T0(2);
  }), new T1(0,function(_e7/* s1ogJ */){
    return (E(_e7/* s1ogJ */)==69) ? E(_dU/* s1og5 */) : new T0(2);
  }));});
},
_e8/* $wa8 */ = function(_e9/* s1odz */){
  var _ea/* s1odA */ = function(_eb/* s1odB */){
    return new F(function(){return A1(_e9/* s1odz */,new T1(1,_eb/* s1odB */));});
  };
  return function(_ec/* s1odD */){
    return (E(_ec/* s1odD */)==46) ? new T1(1,B(_bQ/* Text.Read.Lex.$wa6 */(_cR/* Text.Read.Lex.lvl */, _ea/* s1odA */))) : new T0(2);
  };
},
_ed/* a3 */ = function(_ee/* s1odK */){
  return new T1(0,B(_e8/* Text.Read.Lex.$wa8 */(_ee/* s1odK */)));
},
_ef/* $wa10 */ = function(_eg/* s1ogP */){
  var _eh/* s1oh1 */ = function(_ei/* s1ogQ */){
    var _ej/* s1ogY */ = function(_ek/* s1ogR */){
      return new T1(1,B(_b7/* Text.ParserCombinators.ReadP.$wa */(_dS/* Text.Read.Lex.a26 */, _cN/* Text.Read.Lex.a */, function(_el/* s1ogS */){
        return new F(function(){return A1(_eg/* s1ogP */,new T1(5,new T3(1,_ei/* s1ogQ */,_ek/* s1ogR */,_el/* s1ogS */)));});
      })));
    };
    return new T1(1,B(_b7/* Text.ParserCombinators.ReadP.$wa */(_ed/* Text.Read.Lex.a3 */, _cP/* Text.Read.Lex.a1 */, _ej/* s1ogY */)));
  };
  return new F(function(){return _bQ/* Text.Read.Lex.$wa6 */(_cR/* Text.Read.Lex.lvl */, _eh/* s1oh1 */);});
},
_em/* a27 */ = function(_en/* s1oh2 */){
  return new T1(1,B(_ef/* Text.Read.Lex.$wa10 */(_en/* s1oh2 */)));
},
_eo/* == */ = function(_ep/* scBJ */){
  return E(E(_ep/* scBJ */).a);
},
_eq/* elem */ = function(_er/* s9uW */, _es/* s9uX */, _et/* s9uY */){
  while(1){
    var _eu/* s9uZ */ = E(_et/* s9uY */);
    if(!_eu/* s9uZ */._){
      return false;
    }else{
      if(!B(A3(_eo/* GHC.Classes.== */,_er/* s9uW */, _es/* s9uX */, _eu/* s9uZ */.a))){
        _et/* s9uY */ = _eu/* s9uZ */.b;
        continue;
      }else{
        return true;
      }
    }
  }
},
_ev/* lvl44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!@#$%&*+./<=>?\\^|:-~"));
}),
_ew/* a6 */ = function(_ex/* s1odZ */){
  return new F(function(){return _eq/* GHC.List.elem */(_aD/* GHC.Classes.$fEqChar */, _ex/* s1odZ */, _ev/* Text.Read.Lex.lvl44 */);});
},
_ey/* $wa9 */ = function(_ez/* s1odN */){
  var _eA/* s1odO */ = new T(function(){
    return B(A1(_ez/* s1odN */,_cB/* Text.Read.Lex.lvl42 */));
  }),
  _eB/* s1odP */ = new T(function(){
    return B(A1(_ez/* s1odN */,_cA/* Text.Read.Lex.lvl41 */));
  });
  return function(_eC/* s1odQ */){
    switch(E(_eC/* s1odQ */)){
      case 79:
        return E(_eA/* s1odO */);
      case 88:
        return E(_eB/* s1odP */);
      case 111:
        return E(_eA/* s1odO */);
      case 120:
        return E(_eB/* s1odP */);
      default:
        return new T0(2);
    }
  };
},
_eD/* a4 */ = function(_eE/* s1odV */){
  return new T1(0,B(_ey/* Text.Read.Lex.$wa9 */(_eE/* s1odV */)));
},
_eF/* a5 */ = function(_eG/* s1odY */){
  return new F(function(){return A1(_eG/* s1odY */,_cR/* Text.Read.Lex.lvl */);});
},
_eH/* chr2 */ = function(_eI/* sjTv */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Prelude.chr: bad argument: ", new T(function(){
    return B(_1M/* GHC.Show.$wshowSignedInt */(9, _eI/* sjTv */, _k/* GHC.Types.[] */));
  }))));});
},
_eJ/* integerToInt */ = function(_eK/* s1Rv */){
  var _eL/* s1Rw */ = E(_eK/* s1Rv */);
  if(!_eL/* s1Rw */._){
    return E(_eL/* s1Rw */.a);
  }else{
    return new F(function(){return I_toInt/* EXTERNAL */(_eL/* s1Rw */.a);});
  }
},
_eM/* leInteger */ = function(_eN/* s1Gp */, _eO/* s1Gq */){
  var _eP/* s1Gr */ = E(_eN/* s1Gp */);
  if(!_eP/* s1Gr */._){
    var _eQ/* s1Gs */ = _eP/* s1Gr */.a,
    _eR/* s1Gt */ = E(_eO/* s1Gq */);
    return (_eR/* s1Gt */._==0) ? _eQ/* s1Gs */<=_eR/* s1Gt */.a : I_compareInt/* EXTERNAL */(_eR/* s1Gt */.a, _eQ/* s1Gs */)>=0;
  }else{
    var _eS/* s1GA */ = _eP/* s1Gr */.a,
    _eT/* s1GB */ = E(_eO/* s1Gq */);
    return (_eT/* s1GB */._==0) ? I_compareInt/* EXTERNAL */(_eS/* s1GA */, _eT/* s1GB */.a)<=0 : I_compare/* EXTERNAL */(_eS/* s1GA */, _eT/* s1GB */.a)<=0;
  }
},
_eU/* pfail1 */ = function(_eV/* s1izT */){
  return new T0(2);
},
_eW/* choice */ = function(_eX/* s1iDZ */){
  var _eY/* s1iE0 */ = E(_eX/* s1iDZ */);
  if(!_eY/* s1iE0 */._){
    return E(_eU/* Text.ParserCombinators.ReadP.pfail1 */);
  }else{
    var _eZ/* s1iE1 */ = _eY/* s1iE0 */.a,
    _f0/* s1iE3 */ = E(_eY/* s1iE0 */.b);
    if(!_f0/* s1iE3 */._){
      return E(_eZ/* s1iE1 */);
    }else{
      var _f1/* s1iE6 */ = new T(function(){
        return B(_eW/* Text.ParserCombinators.ReadP.choice */(_f0/* s1iE3 */));
      }),
      _f2/* s1iEa */ = function(_f3/* s1iE7 */){
        return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_eZ/* s1iE1 */,_f3/* s1iE7 */)), new T(function(){
          return B(A1(_f1/* s1iE6 */,_f3/* s1iE7 */));
        }));});
      };
      return E(_f2/* s1iEa */);
    }
  }
},
_f4/* $wa6 */ = function(_f5/* s1izU */, _f6/* s1izV */){
  var _f7/* s1izW */ = function(_f8/* s1izX */, _f9/* s1izY */, _fa/* s1izZ */){
    var _fb/* s1iA0 */ = E(_f8/* s1izX */);
    if(!_fb/* s1iA0 */._){
      return new F(function(){return A1(_fa/* s1izZ */,_f5/* s1izU */);});
    }else{
      var _fc/* s1iA3 */ = E(_f9/* s1izY */);
      if(!_fc/* s1iA3 */._){
        return new T0(2);
      }else{
        if(E(_fb/* s1iA0 */.a)!=E(_fc/* s1iA3 */.a)){
          return new T0(2);
        }else{
          var _fd/* s1iAc */ = new T(function(){
            return B(_f7/* s1izW */(_fb/* s1iA0 */.b, _fc/* s1iA3 */.b, _fa/* s1izZ */));
          });
          return new T1(0,function(_fe/* s1iAd */){
            return E(_fd/* s1iAc */);
          });
        }
      }
    }
  };
  return function(_ff/* s1iAf */){
    return new F(function(){return _f7/* s1izW */(_f5/* s1izU */, _ff/* s1iAf */, _f6/* s1izV */);});
  };
},
_fg/* a28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SO"));
}),
_fh/* lvl29 */ = 14,
_fi/* a29 */ = function(_fj/* s1onM */){
  var _fk/* s1onN */ = new T(function(){
    return B(A1(_fj/* s1onM */,_fh/* Text.Read.Lex.lvl29 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_fg/* Text.Read.Lex.a28 */, function(_fl/* s1onO */){
    return E(_fk/* s1onN */);
  })));
},
_fm/* a30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SOH"));
}),
_fn/* lvl35 */ = 1,
_fo/* a31 */ = function(_fp/* s1onS */){
  var _fq/* s1onT */ = new T(function(){
    return B(A1(_fp/* s1onS */,_fn/* Text.Read.Lex.lvl35 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_fm/* Text.Read.Lex.a30 */, function(_fr/* s1onU */){
    return E(_fq/* s1onT */);
  })));
},
_fs/* a32 */ = function(_ft/* s1onY */){
  return new T1(1,B(_b7/* Text.ParserCombinators.ReadP.$wa */(_fo/* Text.Read.Lex.a31 */, _fi/* Text.Read.Lex.a29 */, _ft/* s1onY */)));
},
_fu/* a33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NUL"));
}),
_fv/* lvl36 */ = 0,
_fw/* a34 */ = function(_fx/* s1oo1 */){
  var _fy/* s1oo2 */ = new T(function(){
    return B(A1(_fx/* s1oo1 */,_fv/* Text.Read.Lex.lvl36 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_fu/* Text.Read.Lex.a33 */, function(_fz/* s1oo3 */){
    return E(_fy/* s1oo2 */);
  })));
},
_fA/* a35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("STX"));
}),
_fB/* lvl34 */ = 2,
_fC/* a36 */ = function(_fD/* s1oo7 */){
  var _fE/* s1oo8 */ = new T(function(){
    return B(A1(_fD/* s1oo7 */,_fB/* Text.Read.Lex.lvl34 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_fA/* Text.Read.Lex.a35 */, function(_fF/* s1oo9 */){
    return E(_fE/* s1oo8 */);
  })));
},
_fG/* a37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETX"));
}),
_fH/* lvl33 */ = 3,
_fI/* a38 */ = function(_fJ/* s1ood */){
  var _fK/* s1ooe */ = new T(function(){
    return B(A1(_fJ/* s1ood */,_fH/* Text.Read.Lex.lvl33 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_fG/* Text.Read.Lex.a37 */, function(_fL/* s1oof */){
    return E(_fK/* s1ooe */);
  })));
},
_fM/* a39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EOT"));
}),
_fN/* lvl32 */ = 4,
_fO/* a40 */ = function(_fP/* s1ooj */){
  var _fQ/* s1ook */ = new T(function(){
    return B(A1(_fP/* s1ooj */,_fN/* Text.Read.Lex.lvl32 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_fM/* Text.Read.Lex.a39 */, function(_fR/* s1ool */){
    return E(_fQ/* s1ook */);
  })));
},
_fS/* a41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ENQ"));
}),
_fT/* lvl31 */ = 5,
_fU/* a42 */ = function(_fV/* s1oop */){
  var _fW/* s1ooq */ = new T(function(){
    return B(A1(_fV/* s1oop */,_fT/* Text.Read.Lex.lvl31 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_fS/* Text.Read.Lex.a41 */, function(_fX/* s1oor */){
    return E(_fW/* s1ooq */);
  })));
},
_fY/* a43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ACK"));
}),
_fZ/* lvl30 */ = 6,
_g0/* a44 */ = function(_g1/* s1oov */){
  var _g2/* s1oow */ = new T(function(){
    return B(A1(_g1/* s1oov */,_fZ/* Text.Read.Lex.lvl30 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_fY/* Text.Read.Lex.a43 */, function(_g3/* s1oox */){
    return E(_g2/* s1oow */);
  })));
},
_g4/* a45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BEL"));
}),
_g5/* lvl7 */ = 7,
_g6/* a46 */ = function(_g7/* s1ooB */){
  var _g8/* s1ooC */ = new T(function(){
    return B(A1(_g7/* s1ooB */,_g5/* Text.Read.Lex.lvl7 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_g4/* Text.Read.Lex.a45 */, function(_g9/* s1ooD */){
    return E(_g8/* s1ooC */);
  })));
},
_ga/* a47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BS"));
}),
_gb/* lvl6 */ = 8,
_gc/* a48 */ = function(_gd/* s1ooH */){
  var _ge/* s1ooI */ = new T(function(){
    return B(A1(_gd/* s1ooH */,_gb/* Text.Read.Lex.lvl6 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_ga/* Text.Read.Lex.a47 */, function(_gf/* s1ooJ */){
    return E(_ge/* s1ooI */);
  })));
},
_gg/* a49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HT"));
}),
_gh/* lvl2 */ = 9,
_gi/* a50 */ = function(_gj/* s1ooN */){
  var _gk/* s1ooO */ = new T(function(){
    return B(A1(_gj/* s1ooN */,_gh/* Text.Read.Lex.lvl2 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_gg/* Text.Read.Lex.a49 */, function(_gl/* s1ooP */){
    return E(_gk/* s1ooO */);
  })));
},
_gm/* a51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LF"));
}),
_gn/* lvl4 */ = 10,
_go/* a52 */ = function(_gp/* s1ooT */){
  var _gq/* s1ooU */ = new T(function(){
    return B(A1(_gp/* s1ooT */,_gn/* Text.Read.Lex.lvl4 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_gm/* Text.Read.Lex.a51 */, function(_gr/* s1ooV */){
    return E(_gq/* s1ooU */);
  })));
},
_gs/* a53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VT"));
}),
_gt/* lvl1 */ = 11,
_gu/* a54 */ = function(_gv/* s1ooZ */){
  var _gw/* s1op0 */ = new T(function(){
    return B(A1(_gv/* s1ooZ */,_gt/* Text.Read.Lex.lvl1 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_gs/* Text.Read.Lex.a53 */, function(_gx/* s1op1 */){
    return E(_gw/* s1op0 */);
  })));
},
_gy/* a55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FF"));
}),
_gz/* lvl5 */ = 12,
_gA/* a56 */ = function(_gB/* s1op5 */){
  var _gC/* s1op6 */ = new T(function(){
    return B(A1(_gB/* s1op5 */,_gz/* Text.Read.Lex.lvl5 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_gy/* Text.Read.Lex.a55 */, function(_gD/* s1op7 */){
    return E(_gC/* s1op6 */);
  })));
},
_gE/* a57 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CR"));
}),
_gF/* lvl3 */ = 13,
_gG/* a58 */ = function(_gH/* s1opb */){
  var _gI/* s1opc */ = new T(function(){
    return B(A1(_gH/* s1opb */,_gF/* Text.Read.Lex.lvl3 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_gE/* Text.Read.Lex.a57 */, function(_gJ/* s1opd */){
    return E(_gI/* s1opc */);
  })));
},
_gK/* a59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SI"));
}),
_gL/* lvl28 */ = 15,
_gM/* a60 */ = function(_gN/* s1oph */){
  var _gO/* s1opi */ = new T(function(){
    return B(A1(_gN/* s1oph */,_gL/* Text.Read.Lex.lvl28 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_gK/* Text.Read.Lex.a59 */, function(_gP/* s1opj */){
    return E(_gO/* s1opi */);
  })));
},
_gQ/* a61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DLE"));
}),
_gR/* lvl27 */ = 16,
_gS/* a62 */ = function(_gT/* s1opn */){
  var _gU/* s1opo */ = new T(function(){
    return B(A1(_gT/* s1opn */,_gR/* Text.Read.Lex.lvl27 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_gQ/* Text.Read.Lex.a61 */, function(_gV/* s1opp */){
    return E(_gU/* s1opo */);
  })));
},
_gW/* a63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC1"));
}),
_gX/* lvl26 */ = 17,
_gY/* a64 */ = function(_gZ/* s1opt */){
  var _h0/* s1opu */ = new T(function(){
    return B(A1(_gZ/* s1opt */,_gX/* Text.Read.Lex.lvl26 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_gW/* Text.Read.Lex.a63 */, function(_h1/* s1opv */){
    return E(_h0/* s1opu */);
  })));
},
_h2/* a65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC2"));
}),
_h3/* lvl25 */ = 18,
_h4/* a66 */ = function(_h5/* s1opz */){
  var _h6/* s1opA */ = new T(function(){
    return B(A1(_h5/* s1opz */,_h3/* Text.Read.Lex.lvl25 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_h2/* Text.Read.Lex.a65 */, function(_h7/* s1opB */){
    return E(_h6/* s1opA */);
  })));
},
_h8/* a67 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC3"));
}),
_h9/* lvl24 */ = 19,
_ha/* a68 */ = function(_hb/* s1opF */){
  var _hc/* s1opG */ = new T(function(){
    return B(A1(_hb/* s1opF */,_h9/* Text.Read.Lex.lvl24 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_h8/* Text.Read.Lex.a67 */, function(_hd/* s1opH */){
    return E(_hc/* s1opG */);
  })));
},
_he/* a69 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC4"));
}),
_hf/* lvl23 */ = 20,
_hg/* a70 */ = function(_hh/* s1opL */){
  var _hi/* s1opM */ = new T(function(){
    return B(A1(_hh/* s1opL */,_hf/* Text.Read.Lex.lvl23 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_he/* Text.Read.Lex.a69 */, function(_hj/* s1opN */){
    return E(_hi/* s1opM */);
  })));
},
_hk/* a71 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NAK"));
}),
_hl/* lvl22 */ = 21,
_hm/* a72 */ = function(_hn/* s1opR */){
  var _ho/* s1opS */ = new T(function(){
    return B(A1(_hn/* s1opR */,_hl/* Text.Read.Lex.lvl22 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_hk/* Text.Read.Lex.a71 */, function(_hp/* s1opT */){
    return E(_ho/* s1opS */);
  })));
},
_hq/* a73 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SYN"));
}),
_hr/* lvl21 */ = 22,
_hs/* a74 */ = function(_ht/* s1opX */){
  var _hu/* s1opY */ = new T(function(){
    return B(A1(_ht/* s1opX */,_hr/* Text.Read.Lex.lvl21 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_hq/* Text.Read.Lex.a73 */, function(_hv/* s1opZ */){
    return E(_hu/* s1opY */);
  })));
},
_hw/* a75 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETB"));
}),
_hx/* lvl20 */ = 23,
_hy/* a76 */ = function(_hz/* s1oq3 */){
  var _hA/* s1oq4 */ = new T(function(){
    return B(A1(_hz/* s1oq3 */,_hx/* Text.Read.Lex.lvl20 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_hw/* Text.Read.Lex.a75 */, function(_hB/* s1oq5 */){
    return E(_hA/* s1oq4 */);
  })));
},
_hC/* a77 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CAN"));
}),
_hD/* lvl19 */ = 24,
_hE/* a78 */ = function(_hF/* s1oq9 */){
  var _hG/* s1oqa */ = new T(function(){
    return B(A1(_hF/* s1oq9 */,_hD/* Text.Read.Lex.lvl19 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_hC/* Text.Read.Lex.a77 */, function(_hH/* s1oqb */){
    return E(_hG/* s1oqa */);
  })));
},
_hI/* a79 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EM"));
}),
_hJ/* lvl18 */ = 25,
_hK/* a80 */ = function(_hL/* s1oqf */){
  var _hM/* s1oqg */ = new T(function(){
    return B(A1(_hL/* s1oqf */,_hJ/* Text.Read.Lex.lvl18 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_hI/* Text.Read.Lex.a79 */, function(_hN/* s1oqh */){
    return E(_hM/* s1oqg */);
  })));
},
_hO/* a81 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SUB"));
}),
_hP/* lvl17 */ = 26,
_hQ/* a82 */ = function(_hR/* s1oql */){
  var _hS/* s1oqm */ = new T(function(){
    return B(A1(_hR/* s1oql */,_hP/* Text.Read.Lex.lvl17 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_hO/* Text.Read.Lex.a81 */, function(_hT/* s1oqn */){
    return E(_hS/* s1oqm */);
  })));
},
_hU/* a83 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ESC"));
}),
_hV/* lvl16 */ = 27,
_hW/* a84 */ = function(_hX/* s1oqr */){
  var _hY/* s1oqs */ = new T(function(){
    return B(A1(_hX/* s1oqr */,_hV/* Text.Read.Lex.lvl16 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_hU/* Text.Read.Lex.a83 */, function(_hZ/* s1oqt */){
    return E(_hY/* s1oqs */);
  })));
},
_i0/* a85 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FS"));
}),
_i1/* lvl15 */ = 28,
_i2/* a86 */ = function(_i3/* s1oqx */){
  var _i4/* s1oqy */ = new T(function(){
    return B(A1(_i3/* s1oqx */,_i1/* Text.Read.Lex.lvl15 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_i0/* Text.Read.Lex.a85 */, function(_i5/* s1oqz */){
    return E(_i4/* s1oqy */);
  })));
},
_i6/* a87 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GS"));
}),
_i7/* lvl14 */ = 29,
_i8/* a88 */ = function(_i9/* s1oqD */){
  var _ia/* s1oqE */ = new T(function(){
    return B(A1(_i9/* s1oqD */,_i7/* Text.Read.Lex.lvl14 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_i6/* Text.Read.Lex.a87 */, function(_ib/* s1oqF */){
    return E(_ia/* s1oqE */);
  })));
},
_ic/* a89 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RS"));
}),
_id/* lvl13 */ = 30,
_ie/* a90 */ = function(_if/* s1oqJ */){
  var _ig/* s1oqK */ = new T(function(){
    return B(A1(_if/* s1oqJ */,_id/* Text.Read.Lex.lvl13 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_ic/* Text.Read.Lex.a89 */, function(_ih/* s1oqL */){
    return E(_ig/* s1oqK */);
  })));
},
_ii/* a91 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("US"));
}),
_ij/* lvl12 */ = 31,
_ik/* a92 */ = function(_il/* s1oqP */){
  var _im/* s1oqQ */ = new T(function(){
    return B(A1(_il/* s1oqP */,_ij/* Text.Read.Lex.lvl12 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_ii/* Text.Read.Lex.a91 */, function(_in/* s1oqR */){
    return E(_im/* s1oqQ */);
  })));
},
_io/* a93 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SP"));
}),
_ip/* x */ = 32,
_iq/* a94 */ = function(_ir/* s1oqV */){
  var _is/* s1oqW */ = new T(function(){
    return B(A1(_ir/* s1oqV */,_ip/* Text.Read.Lex.x */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_io/* Text.Read.Lex.a93 */, function(_it/* s1oqX */){
    return E(_is/* s1oqW */);
  })));
},
_iu/* a95 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DEL"));
}),
_iv/* x1 */ = 127,
_iw/* a96 */ = function(_ix/* s1or1 */){
  var _iy/* s1or2 */ = new T(function(){
    return B(A1(_ix/* s1or1 */,_iv/* Text.Read.Lex.x1 */));
  });
  return new T1(1,B(_f4/* Text.ParserCombinators.ReadP.$wa6 */(_iu/* Text.Read.Lex.a95 */, function(_iz/* s1or3 */){
    return E(_iy/* s1or2 */);
  })));
},
_iA/* lvl47 */ = new T2(1,_iw/* Text.Read.Lex.a96 */,_k/* GHC.Types.[] */),
_iB/* lvl48 */ = new T2(1,_iq/* Text.Read.Lex.a94 */,_iA/* Text.Read.Lex.lvl47 */),
_iC/* lvl49 */ = new T2(1,_ik/* Text.Read.Lex.a92 */,_iB/* Text.Read.Lex.lvl48 */),
_iD/* lvl50 */ = new T2(1,_ie/* Text.Read.Lex.a90 */,_iC/* Text.Read.Lex.lvl49 */),
_iE/* lvl51 */ = new T2(1,_i8/* Text.Read.Lex.a88 */,_iD/* Text.Read.Lex.lvl50 */),
_iF/* lvl52 */ = new T2(1,_i2/* Text.Read.Lex.a86 */,_iE/* Text.Read.Lex.lvl51 */),
_iG/* lvl53 */ = new T2(1,_hW/* Text.Read.Lex.a84 */,_iF/* Text.Read.Lex.lvl52 */),
_iH/* lvl54 */ = new T2(1,_hQ/* Text.Read.Lex.a82 */,_iG/* Text.Read.Lex.lvl53 */),
_iI/* lvl55 */ = new T2(1,_hK/* Text.Read.Lex.a80 */,_iH/* Text.Read.Lex.lvl54 */),
_iJ/* lvl56 */ = new T2(1,_hE/* Text.Read.Lex.a78 */,_iI/* Text.Read.Lex.lvl55 */),
_iK/* lvl57 */ = new T2(1,_hy/* Text.Read.Lex.a76 */,_iJ/* Text.Read.Lex.lvl56 */),
_iL/* lvl58 */ = new T2(1,_hs/* Text.Read.Lex.a74 */,_iK/* Text.Read.Lex.lvl57 */),
_iM/* lvl59 */ = new T2(1,_hm/* Text.Read.Lex.a72 */,_iL/* Text.Read.Lex.lvl58 */),
_iN/* lvl60 */ = new T2(1,_hg/* Text.Read.Lex.a70 */,_iM/* Text.Read.Lex.lvl59 */),
_iO/* lvl61 */ = new T2(1,_ha/* Text.Read.Lex.a68 */,_iN/* Text.Read.Lex.lvl60 */),
_iP/* lvl62 */ = new T2(1,_h4/* Text.Read.Lex.a66 */,_iO/* Text.Read.Lex.lvl61 */),
_iQ/* lvl63 */ = new T2(1,_gY/* Text.Read.Lex.a64 */,_iP/* Text.Read.Lex.lvl62 */),
_iR/* lvl64 */ = new T2(1,_gS/* Text.Read.Lex.a62 */,_iQ/* Text.Read.Lex.lvl63 */),
_iS/* lvl65 */ = new T2(1,_gM/* Text.Read.Lex.a60 */,_iR/* Text.Read.Lex.lvl64 */),
_iT/* lvl66 */ = new T2(1,_gG/* Text.Read.Lex.a58 */,_iS/* Text.Read.Lex.lvl65 */),
_iU/* lvl67 */ = new T2(1,_gA/* Text.Read.Lex.a56 */,_iT/* Text.Read.Lex.lvl66 */),
_iV/* lvl68 */ = new T2(1,_gu/* Text.Read.Lex.a54 */,_iU/* Text.Read.Lex.lvl67 */),
_iW/* lvl69 */ = new T2(1,_go/* Text.Read.Lex.a52 */,_iV/* Text.Read.Lex.lvl68 */),
_iX/* lvl70 */ = new T2(1,_gi/* Text.Read.Lex.a50 */,_iW/* Text.Read.Lex.lvl69 */),
_iY/* lvl71 */ = new T2(1,_gc/* Text.Read.Lex.a48 */,_iX/* Text.Read.Lex.lvl70 */),
_iZ/* lvl72 */ = new T2(1,_g6/* Text.Read.Lex.a46 */,_iY/* Text.Read.Lex.lvl71 */),
_j0/* lvl73 */ = new T2(1,_g0/* Text.Read.Lex.a44 */,_iZ/* Text.Read.Lex.lvl72 */),
_j1/* lvl74 */ = new T2(1,_fU/* Text.Read.Lex.a42 */,_j0/* Text.Read.Lex.lvl73 */),
_j2/* lvl75 */ = new T2(1,_fO/* Text.Read.Lex.a40 */,_j1/* Text.Read.Lex.lvl74 */),
_j3/* lvl76 */ = new T2(1,_fI/* Text.Read.Lex.a38 */,_j2/* Text.Read.Lex.lvl75 */),
_j4/* lvl77 */ = new T2(1,_fC/* Text.Read.Lex.a36 */,_j3/* Text.Read.Lex.lvl76 */),
_j5/* lvl78 */ = new T2(1,_fw/* Text.Read.Lex.a34 */,_j4/* Text.Read.Lex.lvl77 */),
_j6/* lvl79 */ = new T2(1,_fs/* Text.Read.Lex.a32 */,_j5/* Text.Read.Lex.lvl78 */),
_j7/* lexAscii */ = new T(function(){
  return B(_eW/* Text.ParserCombinators.ReadP.choice */(_j6/* Text.Read.Lex.lvl79 */));
}),
_j8/* lvl10 */ = 34,
_j9/* lvl11 */ = new T1(0,1114111),
_ja/* lvl8 */ = 92,
_jb/* lvl9 */ = 39,
_jc/* lexChar2 */ = function(_jd/* s1or7 */){
  var _je/* s1or8 */ = new T(function(){
    return B(A1(_jd/* s1or7 */,_g5/* Text.Read.Lex.lvl7 */));
  }),
  _jf/* s1or9 */ = new T(function(){
    return B(A1(_jd/* s1or7 */,_gb/* Text.Read.Lex.lvl6 */));
  }),
  _jg/* s1ora */ = new T(function(){
    return B(A1(_jd/* s1or7 */,_gh/* Text.Read.Lex.lvl2 */));
  }),
  _jh/* s1orb */ = new T(function(){
    return B(A1(_jd/* s1or7 */,_gn/* Text.Read.Lex.lvl4 */));
  }),
  _ji/* s1orc */ = new T(function(){
    return B(A1(_jd/* s1or7 */,_gt/* Text.Read.Lex.lvl1 */));
  }),
  _jj/* s1ord */ = new T(function(){
    return B(A1(_jd/* s1or7 */,_gz/* Text.Read.Lex.lvl5 */));
  }),
  _jk/* s1ore */ = new T(function(){
    return B(A1(_jd/* s1or7 */,_gF/* Text.Read.Lex.lvl3 */));
  }),
  _jl/* s1orf */ = new T(function(){
    return B(A1(_jd/* s1or7 */,_ja/* Text.Read.Lex.lvl8 */));
  }),
  _jm/* s1org */ = new T(function(){
    return B(A1(_jd/* s1or7 */,_jb/* Text.Read.Lex.lvl9 */));
  }),
  _jn/* s1orh */ = new T(function(){
    return B(A1(_jd/* s1or7 */,_j8/* Text.Read.Lex.lvl10 */));
  }),
  _jo/* s1osl */ = new T(function(){
    var _jp/* s1orE */ = function(_jq/* s1oro */){
      var _jr/* s1orp */ = new T(function(){
        return B(_de/* GHC.Integer.Type.smallInteger */(E(_jq/* s1oro */)));
      }),
      _js/* s1orB */ = function(_jt/* s1ors */){
        var _ju/* s1ort */ = B(_dP/* Text.Read.Lex.valInteger */(_jr/* s1orp */, _jt/* s1ors */));
        if(!B(_eM/* GHC.Integer.Type.leInteger */(_ju/* s1ort */, _j9/* Text.Read.Lex.lvl11 */))){
          return new T0(2);
        }else{
          return new F(function(){return A1(_jd/* s1or7 */,new T(function(){
            var _jv/* s1orv */ = B(_eJ/* GHC.Integer.Type.integerToInt */(_ju/* s1ort */));
            if(_jv/* s1orv */>>>0>1114111){
              return B(_eH/* GHC.Char.chr2 */(_jv/* s1orv */));
            }else{
              return _jv/* s1orv */;
            }
          }));});
        }
      };
      return new T1(1,B(_bQ/* Text.Read.Lex.$wa6 */(_jq/* s1oro */, _js/* s1orB */)));
    },
    _jw/* s1osk */ = new T(function(){
      var _jx/* s1orI */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_ij/* Text.Read.Lex.lvl12 */));
      }),
      _jy/* s1orJ */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_id/* Text.Read.Lex.lvl13 */));
      }),
      _jz/* s1orK */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_i7/* Text.Read.Lex.lvl14 */));
      }),
      _jA/* s1orL */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_i1/* Text.Read.Lex.lvl15 */));
      }),
      _jB/* s1orM */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_hV/* Text.Read.Lex.lvl16 */));
      }),
      _jC/* s1orN */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_hP/* Text.Read.Lex.lvl17 */));
      }),
      _jD/* s1orO */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_hJ/* Text.Read.Lex.lvl18 */));
      }),
      _jE/* s1orP */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_hD/* Text.Read.Lex.lvl19 */));
      }),
      _jF/* s1orQ */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_hx/* Text.Read.Lex.lvl20 */));
      }),
      _jG/* s1orR */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_hr/* Text.Read.Lex.lvl21 */));
      }),
      _jH/* s1orS */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_hl/* Text.Read.Lex.lvl22 */));
      }),
      _jI/* s1orT */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_hf/* Text.Read.Lex.lvl23 */));
      }),
      _jJ/* s1orU */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_h9/* Text.Read.Lex.lvl24 */));
      }),
      _jK/* s1orV */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_h3/* Text.Read.Lex.lvl25 */));
      }),
      _jL/* s1orW */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_gX/* Text.Read.Lex.lvl26 */));
      }),
      _jM/* s1orX */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_gR/* Text.Read.Lex.lvl27 */));
      }),
      _jN/* s1orY */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_gL/* Text.Read.Lex.lvl28 */));
      }),
      _jO/* s1orZ */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_fh/* Text.Read.Lex.lvl29 */));
      }),
      _jP/* s1os0 */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_fZ/* Text.Read.Lex.lvl30 */));
      }),
      _jQ/* s1os1 */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_fT/* Text.Read.Lex.lvl31 */));
      }),
      _jR/* s1os2 */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_fN/* Text.Read.Lex.lvl32 */));
      }),
      _jS/* s1os3 */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_fH/* Text.Read.Lex.lvl33 */));
      }),
      _jT/* s1os4 */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_fB/* Text.Read.Lex.lvl34 */));
      }),
      _jU/* s1os5 */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_fn/* Text.Read.Lex.lvl35 */));
      }),
      _jV/* s1os6 */ = new T(function(){
        return B(A1(_jd/* s1or7 */,_fv/* Text.Read.Lex.lvl36 */));
      }),
      _jW/* s1os7 */ = function(_jX/* s1os8 */){
        switch(E(_jX/* s1os8 */)){
          case 64:
            return E(_jV/* s1os6 */);
          case 65:
            return E(_jU/* s1os5 */);
          case 66:
            return E(_jT/* s1os4 */);
          case 67:
            return E(_jS/* s1os3 */);
          case 68:
            return E(_jR/* s1os2 */);
          case 69:
            return E(_jQ/* s1os1 */);
          case 70:
            return E(_jP/* s1os0 */);
          case 71:
            return E(_je/* s1or8 */);
          case 72:
            return E(_jf/* s1or9 */);
          case 73:
            return E(_jg/* s1ora */);
          case 74:
            return E(_jh/* s1orb */);
          case 75:
            return E(_ji/* s1orc */);
          case 76:
            return E(_jj/* s1ord */);
          case 77:
            return E(_jk/* s1ore */);
          case 78:
            return E(_jO/* s1orZ */);
          case 79:
            return E(_jN/* s1orY */);
          case 80:
            return E(_jM/* s1orX */);
          case 81:
            return E(_jL/* s1orW */);
          case 82:
            return E(_jK/* s1orV */);
          case 83:
            return E(_jJ/* s1orU */);
          case 84:
            return E(_jI/* s1orT */);
          case 85:
            return E(_jH/* s1orS */);
          case 86:
            return E(_jG/* s1orR */);
          case 87:
            return E(_jF/* s1orQ */);
          case 88:
            return E(_jE/* s1orP */);
          case 89:
            return E(_jD/* s1orO */);
          case 90:
            return E(_jC/* s1orN */);
          case 91:
            return E(_jB/* s1orM */);
          case 92:
            return E(_jA/* s1orL */);
          case 93:
            return E(_jz/* s1orK */);
          case 94:
            return E(_jy/* s1orJ */);
          case 95:
            return E(_jx/* s1orI */);
          default:
            return new T0(2);
        }
      };
      return B(_9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_jY/* s1osd */){
        return (E(_jY/* s1osd */)==94) ? E(new T1(0,_jW/* s1os7 */)) : new T0(2);
      }), new T(function(){
        return B(A1(_j7/* Text.Read.Lex.lexAscii */,_jd/* s1or7 */));
      })));
    });
    return B(_9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,B(_b7/* Text.ParserCombinators.ReadP.$wa */(_eD/* Text.Read.Lex.a4 */, _eF/* Text.Read.Lex.a5 */, _jp/* s1orE */))), _jw/* s1osk */));
  });
  return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_jZ/* s1ori */){
    switch(E(_jZ/* s1ori */)){
      case 34:
        return E(_jn/* s1orh */);
      case 39:
        return E(_jm/* s1org */);
      case 92:
        return E(_jl/* s1orf */);
      case 97:
        return E(_je/* s1or8 */);
      case 98:
        return E(_jf/* s1or9 */);
      case 102:
        return E(_jj/* s1ord */);
      case 110:
        return E(_jh/* s1orb */);
      case 114:
        return E(_jk/* s1ore */);
      case 116:
        return E(_jg/* s1ora */);
      case 118:
        return E(_ji/* s1orc */);
      default:
        return new T0(2);
    }
  }), _jo/* s1osl */);});
},
_k0/* a */ = function(_k1/* s1iyn */){
  return new F(function(){return A1(_k1/* s1iyn */,_0/* GHC.Tuple.() */);});
},
_k2/* skipSpaces_skip */ = function(_k3/* s1iIB */){
  var _k4/* s1iIC */ = E(_k3/* s1iIB */);
  if(!_k4/* s1iIC */._){
    return E(_k0/* Text.ParserCombinators.ReadP.a */);
  }else{
    var _k5/* s1iIF */ = E(_k4/* s1iIC */.a),
    _k6/* s1iIH */ = _k5/* s1iIF */>>>0,
    _k7/* s1iIJ */ = new T(function(){
      return B(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */(_k4/* s1iIC */.b));
    });
    if(_k6/* s1iIH */>887){
      var _k8/* s1iIO */ = u_iswspace/* EXTERNAL */(_k5/* s1iIF */);
      if(!E(_k8/* s1iIO */)){
        return E(_k0/* Text.ParserCombinators.ReadP.a */);
      }else{
        var _k9/* s1iIW */ = function(_ka/* s1iIS */){
          var _kb/* s1iIT */ = new T(function(){
            return B(A1(_k7/* s1iIJ */,_ka/* s1iIS */));
          });
          return new T1(0,function(_kc/* s1iIU */){
            return E(_kb/* s1iIT */);
          });
        };
        return E(_k9/* s1iIW */);
      }
    }else{
      var _kd/* s1iIX */ = E(_k6/* s1iIH */);
      if(_kd/* s1iIX */==32){
        var _ke/* s1iJg */ = function(_kf/* s1iJc */){
          var _kg/* s1iJd */ = new T(function(){
            return B(A1(_k7/* s1iIJ */,_kf/* s1iJc */));
          });
          return new T1(0,function(_kh/* s1iJe */){
            return E(_kg/* s1iJd */);
          });
        };
        return E(_ke/* s1iJg */);
      }else{
        if(_kd/* s1iIX */-9>>>0>4){
          if(E(_kd/* s1iIX */)==160){
            var _ki/* s1iJ6 */ = function(_kj/* s1iJ2 */){
              var _kk/* s1iJ3 */ = new T(function(){
                return B(A1(_k7/* s1iIJ */,_kj/* s1iJ2 */));
              });
              return new T1(0,function(_kl/* s1iJ4 */){
                return E(_kk/* s1iJ3 */);
              });
            };
            return E(_ki/* s1iJ6 */);
          }else{
            return E(_k0/* Text.ParserCombinators.ReadP.a */);
          }
        }else{
          var _km/* s1iJb */ = function(_kn/* s1iJ7 */){
            var _ko/* s1iJ8 */ = new T(function(){
              return B(A1(_k7/* s1iIJ */,_kn/* s1iJ7 */));
            });
            return new T1(0,function(_kp/* s1iJ9 */){
              return E(_ko/* s1iJ8 */);
            });
          };
          return E(_km/* s1iJb */);
        }
      }
    }
  }
},
_kq/* a97 */ = function(_kr/* s1osm */){
  var _ks/* s1osn */ = new T(function(){
    return B(_kq/* Text.Read.Lex.a97 */(_kr/* s1osm */));
  }),
  _kt/* s1oso */ = function(_ku/* s1osp */){
    return (E(_ku/* s1osp */)==92) ? E(_ks/* s1osn */) : new T0(2);
  },
  _kv/* s1osu */ = function(_kw/* s1osv */){
    return E(new T1(0,_kt/* s1oso */));
  },
  _kx/* s1osy */ = new T1(1,function(_ky/* s1osx */){
    return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_ky/* s1osx */, _kv/* s1osu */);});
  }),
  _kz/* s1osz */ = new T(function(){
    return B(_jc/* Text.Read.Lex.lexChar2 */(function(_kA/* s1osA */){
      return new F(function(){return A1(_kr/* s1osm */,new T2(0,_kA/* s1osA */,_8G/* GHC.Types.True */));});
    }));
  }),
  _kB/* s1osD */ = function(_kC/* s1osE */){
    var _kD/* s1osH */ = E(_kC/* s1osE */);
    if(_kD/* s1osH */==38){
      return E(_ks/* s1osn */);
    }else{
      var _kE/* s1osI */ = _kD/* s1osH */>>>0;
      if(_kE/* s1osI */>887){
        var _kF/* s1osO */ = u_iswspace/* EXTERNAL */(_kD/* s1osH */);
        return (E(_kF/* s1osO */)==0) ? new T0(2) : E(_kx/* s1osy */);
      }else{
        var _kG/* s1osS */ = E(_kE/* s1osI */);
        return (_kG/* s1osS */==32) ? E(_kx/* s1osy */) : (_kG/* s1osS */-9>>>0>4) ? (E(_kG/* s1osS */)==160) ? E(_kx/* s1osy */) : new T0(2) : E(_kx/* s1osy */);
      }
    }
  };
  return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_kH/* s1osY */){
    return (E(_kH/* s1osY */)==92) ? E(new T1(0,_kB/* s1osD */)) : new T0(2);
  }), new T1(0,function(_kI/* s1ot4 */){
    var _kJ/* s1ot5 */ = E(_kI/* s1ot4 */);
    if(E(_kJ/* s1ot5 */)==92){
      return E(_kz/* s1osz */);
    }else{
      return new F(function(){return A1(_kr/* s1osm */,new T2(0,_kJ/* s1ot5 */,_4x/* GHC.Types.False */));});
    }
  }));});
},
_kK/* a98 */ = function(_kL/* s1otb */, _kM/* s1otc */){
  var _kN/* s1otd */ = new T(function(){
    return B(A1(_kM/* s1otc */,new T1(1,new T(function(){
      return B(A1(_kL/* s1otb */,_k/* GHC.Types.[] */));
    }))));
  }),
  _kO/* s1otu */ = function(_kP/* s1otg */){
    var _kQ/* s1oth */ = E(_kP/* s1otg */),
    _kR/* s1otk */ = E(_kQ/* s1oth */.a);
    if(E(_kR/* s1otk */)==34){
      if(!E(_kQ/* s1oth */.b)){
        return E(_kN/* s1otd */);
      }else{
        return new F(function(){return _kK/* Text.Read.Lex.a98 */(function(_kS/* s1otr */){
          return new F(function(){return A1(_kL/* s1otb */,new T2(1,_kR/* s1otk */,_kS/* s1otr */));});
        }, _kM/* s1otc */);});
      }
    }else{
      return new F(function(){return _kK/* Text.Read.Lex.a98 */(function(_kT/* s1otn */){
        return new F(function(){return A1(_kL/* s1otb */,new T2(1,_kR/* s1otk */,_kT/* s1otn */));});
      }, _kM/* s1otc */);});
    }
  };
  return new F(function(){return _kq/* Text.Read.Lex.a97 */(_kO/* s1otu */);});
},
_kU/* lvl45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_\'"));
}),
_kV/* $wisIdfChar */ = function(_kW/* s1otE */){
  var _kX/* s1otH */ = u_iswalnum/* EXTERNAL */(_kW/* s1otE */);
  if(!E(_kX/* s1otH */)){
    return new F(function(){return _eq/* GHC.List.elem */(_aD/* GHC.Classes.$fEqChar */, _kW/* s1otE */, _kU/* Text.Read.Lex.lvl45 */);});
  }else{
    return true;
  }
},
_kY/* isIdfChar */ = function(_kZ/* s1otM */){
  return new F(function(){return _kV/* Text.Read.Lex.$wisIdfChar */(E(_kZ/* s1otM */));});
},
_l0/* lvl43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(",;()[]{}`"));
}),
_l1/* a7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("=>"));
}),
_l2/* a8 */ = new T2(1,_l1/* Text.Read.Lex.a7 */,_k/* GHC.Types.[] */),
_l3/* a9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("~"));
}),
_l4/* a10 */ = new T2(1,_l3/* Text.Read.Lex.a9 */,_l2/* Text.Read.Lex.a8 */),
_l5/* a11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("@"));
}),
_l6/* a12 */ = new T2(1,_l5/* Text.Read.Lex.a11 */,_l4/* Text.Read.Lex.a10 */),
_l7/* a13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("->"));
}),
_l8/* a14 */ = new T2(1,_l7/* Text.Read.Lex.a13 */,_l6/* Text.Read.Lex.a12 */),
_l9/* a15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<-"));
}),
_la/* a16 */ = new T2(1,_l9/* Text.Read.Lex.a15 */,_l8/* Text.Read.Lex.a14 */),
_lb/* a17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("|"));
}),
_lc/* a18 */ = new T2(1,_lb/* Text.Read.Lex.a17 */,_la/* Text.Read.Lex.a16 */),
_ld/* a19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\"));
}),
_le/* a20 */ = new T2(1,_ld/* Text.Read.Lex.a19 */,_lc/* Text.Read.Lex.a18 */),
_lf/* a21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("="));
}),
_lg/* a22 */ = new T2(1,_lf/* Text.Read.Lex.a21 */,_le/* Text.Read.Lex.a20 */),
_lh/* a23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("::"));
}),
_li/* a24 */ = new T2(1,_lh/* Text.Read.Lex.a23 */,_lg/* Text.Read.Lex.a22 */),
_lj/* a25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".."));
}),
_lk/* reserved_ops */ = new T2(1,_lj/* Text.Read.Lex.a25 */,_li/* Text.Read.Lex.a24 */),
_ll/* expect2 */ = function(_lm/* s1otP */){
  var _ln/* s1otQ */ = new T(function(){
    return B(A1(_lm/* s1otP */,_bL/* Text.Read.Lex.EOF */));
  }),
  _lo/* s1ovk */ = new T(function(){
    var _lp/* s1otX */ = new T(function(){
      var _lq/* s1ou6 */ = function(_lr/* s1otY */){
        var _ls/* s1otZ */ = new T(function(){
          return B(A1(_lm/* s1otP */,new T1(0,_lr/* s1otY */)));
        });
        return new T1(0,function(_lt/* s1ou1 */){
          return (E(_lt/* s1ou1 */)==39) ? E(_ls/* s1otZ */) : new T0(2);
        });
      };
      return B(_jc/* Text.Read.Lex.lexChar2 */(_lq/* s1ou6 */));
    }),
    _lu/* s1ou7 */ = function(_lv/* s1ou8 */){
      var _lw/* s1ou9 */ = E(_lv/* s1ou8 */);
      switch(E(_lw/* s1ou9 */)){
        case 39:
          return new T0(2);
        case 92:
          return E(_lp/* s1otX */);
        default:
          var _lx/* s1ouc */ = new T(function(){
            return B(A1(_lm/* s1otP */,new T1(0,_lw/* s1ou9 */)));
          });
          return new T1(0,function(_ly/* s1oue */){
            return (E(_ly/* s1oue */)==39) ? E(_lx/* s1ouc */) : new T0(2);
          });
      }
    },
    _lz/* s1ovj */ = new T(function(){
      var _lA/* s1ouq */ = new T(function(){
        return B(_kK/* Text.Read.Lex.a98 */(_bM/* GHC.Base.id */, _lm/* s1otP */));
      }),
      _lB/* s1ovi */ = new T(function(){
        var _lC/* s1ovh */ = new T(function(){
          var _lD/* s1ovg */ = new T(function(){
            var _lE/* s1ovb */ = function(_lF/* s1ouP */){
              var _lG/* s1ouQ */ = E(_lF/* s1ouP */),
              _lH/* s1ouU */ = u_iswalpha/* EXTERNAL */(_lG/* s1ouQ */);
              return (E(_lH/* s1ouU */)==0) ? (E(_lG/* s1ouQ */)==95) ? new T1(1,B(_bx/* Text.ParserCombinators.ReadP.$wa3 */(_kY/* Text.Read.Lex.isIdfChar */, function(_lI/* s1ov5 */){
                return new F(function(){return A1(_lm/* s1otP */,new T1(3,new T2(1,_lG/* s1ouQ */,_lI/* s1ov5 */)));});
              }))) : new T0(2) : new T1(1,B(_bx/* Text.ParserCombinators.ReadP.$wa3 */(_kY/* Text.Read.Lex.isIdfChar */, function(_lJ/* s1ouY */){
                return new F(function(){return A1(_lm/* s1otP */,new T1(3,new T2(1,_lG/* s1ouQ */,_lJ/* s1ouY */)));});
              })));
            };
            return B(_9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,_lE/* s1ovb */), new T(function(){
              return new T1(1,B(_b7/* Text.ParserCombinators.ReadP.$wa */(_cL/* Text.Read.Lex.a2 */, _em/* Text.Read.Lex.a27 */, _lm/* s1otP */)));
            })));
          }),
          _lK/* s1ouN */ = function(_lL/* s1ouD */){
            return (!B(_eq/* GHC.List.elem */(_aD/* GHC.Classes.$fEqChar */, _lL/* s1ouD */, _ev/* Text.Read.Lex.lvl44 */))) ? new T0(2) : new T1(1,B(_bx/* Text.ParserCombinators.ReadP.$wa3 */(_ew/* Text.Read.Lex.a6 */, function(_lM/* s1ouF */){
              var _lN/* s1ouG */ = new T2(1,_lL/* s1ouD */,_lM/* s1ouF */);
              if(!B(_eq/* GHC.List.elem */(_aM/* GHC.Classes.$fEq[]_$s$fEq[]1 */, _lN/* s1ouG */, _lk/* Text.Read.Lex.reserved_ops */))){
                return new F(function(){return A1(_lm/* s1otP */,new T1(4,_lN/* s1ouG */));});
              }else{
                return new F(function(){return A1(_lm/* s1otP */,new T1(2,_lN/* s1ouG */));});
              }
            })));
          };
          return B(_9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,_lK/* s1ouN */), _lD/* s1ovg */));
        });
        return B(_9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_lO/* s1oux */){
          if(!B(_eq/* GHC.List.elem */(_aD/* GHC.Classes.$fEqChar */, _lO/* s1oux */, _l0/* Text.Read.Lex.lvl43 */))){
            return new T0(2);
          }else{
            return new F(function(){return A1(_lm/* s1otP */,new T1(2,new T2(1,_lO/* s1oux */,_k/* GHC.Types.[] */)));});
          }
        }), _lC/* s1ovh */));
      });
      return B(_9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_lP/* s1our */){
        return (E(_lP/* s1our */)==34) ? E(_lA/* s1ouq */) : new T0(2);
      }), _lB/* s1ovi */));
    });
    return B(_9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_lQ/* s1ouk */){
      return (E(_lQ/* s1ouk */)==39) ? E(new T1(0,_lu/* s1ou7 */)) : new T0(2);
    }), _lz/* s1ovj */));
  });
  return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_lR/* s1otR */){
    return (E(_lR/* s1otR */)._==0) ? E(_ln/* s1otQ */) : new T0(2);
  }), _lo/* s1ovk */);});
},
_lS/* minPrec */ = 0,
_lT/* $wa3 */ = function(_lU/* s1viS */, _lV/* s1viT */){
  var _lW/* s1viU */ = new T(function(){
    var _lX/* s1viV */ = new T(function(){
      var _lY/* s1vj8 */ = function(_lZ/* s1viW */){
        var _m0/* s1viX */ = new T(function(){
          var _m1/* s1viY */ = new T(function(){
            return B(A1(_lV/* s1viT */,_lZ/* s1viW */));
          });
          return B(_ll/* Text.Read.Lex.expect2 */(function(_m2/* s1viZ */){
            var _m3/* s1vj0 */ = E(_m2/* s1viZ */);
            return (_m3/* s1vj0 */._==2) ? (!B(_2n/* GHC.Base.eqString */(_m3/* s1vj0 */.a, _aw/* GHC.Read.$fRead(,)4 */))) ? new T0(2) : E(_m1/* s1viY */) : new T0(2);
          }));
        }),
        _m4/* s1vj4 */ = function(_m5/* s1vj5 */){
          return E(_m0/* s1viX */);
        };
        return new T1(1,function(_m6/* s1vj6 */){
          return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_m6/* s1vj6 */, _m4/* s1vj4 */);});
        });
      };
      return B(A2(_lU/* s1viS */,_lS/* Text.ParserCombinators.ReadPrec.minPrec */, _lY/* s1vj8 */));
    });
    return B(_ll/* Text.Read.Lex.expect2 */(function(_m7/* s1vj9 */){
      var _m8/* s1vja */ = E(_m7/* s1vj9 */);
      return (_m8/* s1vja */._==2) ? (!B(_2n/* GHC.Base.eqString */(_m8/* s1vja */.a, _av/* GHC.Read.$fRead(,)3 */))) ? new T0(2) : E(_lX/* s1viV */) : new T0(2);
    }));
  }),
  _m9/* s1vje */ = function(_ma/* s1vjf */){
    return E(_lW/* s1viU */);
  };
  return function(_mb/* s1vjg */){
    return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_mb/* s1vjg */, _m9/* s1vje */);});
  };
},
_mc/* $fReadDouble10 */ = function(_md/* s1vjn */, _me/* s1vjo */){
  var _mf/* s1vjp */ = function(_mg/* s1vjq */){
    var _mh/* s1vjr */ = new T(function(){
      return B(A1(_md/* s1vjn */,_mg/* s1vjq */));
    }),
    _mi/* s1vjx */ = function(_mj/* s1vjs */){
      return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_mh/* s1vjr */,_mj/* s1vjs */)), new T(function(){
        return new T1(1,B(_lT/* GHC.Read.$wa3 */(_mf/* s1vjp */, _mj/* s1vjs */)));
      }));});
    };
    return E(_mi/* s1vjx */);
  },
  _mk/* s1vjy */ = new T(function(){
    return B(A1(_md/* s1vjn */,_me/* s1vjo */));
  }),
  _ml/* s1vjE */ = function(_mm/* s1vjz */){
    return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_mk/* s1vjy */,_mm/* s1vjz */)), new T(function(){
      return new T1(1,B(_lT/* GHC.Read.$wa3 */(_mf/* s1vjp */, _mm/* s1vjz */)));
    }));});
  };
  return E(_ml/* s1vjE */);
},
_mn/* $fReadInt3 */ = function(_mo/* s1vlT */, _mp/* s1vlU */){
  var _mq/* s1vmt */ = function(_mr/* s1vlV */, _ms/* s1vlW */){
    var _mt/* s1vlX */ = function(_mu/* s1vlY */){
      return new F(function(){return A1(_ms/* s1vlW */,new T(function(){
        return  -E(_mu/* s1vlY */);
      }));});
    },
    _mv/* s1vm5 */ = new T(function(){
      return B(_ll/* Text.Read.Lex.expect2 */(function(_mw/* s1vm4 */){
        return new F(function(){return A3(_mo/* s1vlT */,_mw/* s1vm4 */, _mr/* s1vlV */, _mt/* s1vlX */);});
      }));
    }),
    _mx/* s1vm6 */ = function(_my/* s1vm7 */){
      return E(_mv/* s1vm5 */);
    },
    _mz/* s1vm8 */ = function(_mA/* s1vm9 */){
      return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_mA/* s1vm9 */, _mx/* s1vm6 */);});
    },
    _mB/* s1vmo */ = new T(function(){
      return B(_ll/* Text.Read.Lex.expect2 */(function(_mC/* s1vmc */){
        var _mD/* s1vmd */ = E(_mC/* s1vmc */);
        if(_mD/* s1vmd */._==4){
          var _mE/* s1vmf */ = E(_mD/* s1vmd */.a);
          if(!_mE/* s1vmf */._){
            return new F(function(){return A3(_mo/* s1vlT */,_mD/* s1vmd */, _mr/* s1vlV */, _ms/* s1vlW */);});
          }else{
            if(E(_mE/* s1vmf */.a)==45){
              if(!E(_mE/* s1vmf */.b)._){
                return E(new T1(1,_mz/* s1vm8 */));
              }else{
                return new F(function(){return A3(_mo/* s1vlT */,_mD/* s1vmd */, _mr/* s1vlV */, _ms/* s1vlW */);});
              }
            }else{
              return new F(function(){return A3(_mo/* s1vlT */,_mD/* s1vmd */, _mr/* s1vlV */, _ms/* s1vlW */);});
            }
          }
        }else{
          return new F(function(){return A3(_mo/* s1vlT */,_mD/* s1vmd */, _mr/* s1vlV */, _ms/* s1vlW */);});
        }
      }));
    }),
    _mF/* s1vmp */ = function(_mG/* s1vmq */){
      return E(_mB/* s1vmo */);
    };
    return new T1(1,function(_mH/* s1vmr */){
      return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_mH/* s1vmr */, _mF/* s1vmp */);});
    });
  };
  return new F(function(){return _mc/* GHC.Read.$fReadDouble10 */(_mq/* s1vmt */, _mp/* s1vlU */);});
},
_mI/* numberToInteger */ = function(_mJ/* s1ojv */){
  var _mK/* s1ojw */ = E(_mJ/* s1ojv */);
  if(!_mK/* s1ojw */._){
    var _mL/* s1ojy */ = _mK/* s1ojw */.b,
    _mM/* s1ojF */ = new T(function(){
      return B(_dy/* Text.Read.Lex.numberToFixed_go */(new T(function(){
        return B(_de/* GHC.Integer.Type.smallInteger */(E(_mK/* s1ojw */.a)));
      }), new T(function(){
        return B(_d9/* GHC.List.$wlenAcc */(_mL/* s1ojy */, 0));
      },1), B(_8H/* GHC.Base.map */(_dg/* Text.Read.Lex.numberToFixed2 */, _mL/* s1ojy */))));
    });
    return new T1(1,_mM/* s1ojF */);
  }else{
    return (E(_mK/* s1ojw */.b)._==0) ? (E(_mK/* s1ojw */.c)._==0) ? new T1(1,new T(function(){
      return B(_dP/* Text.Read.Lex.valInteger */(_d8/* Text.Read.Lex.numberToFixed1 */, _mK/* s1ojw */.a));
    })) : __Z/* EXTERNAL */ : __Z/* EXTERNAL */;
  }
},
_mN/* pfail1 */ = function(_mO/* s1kH8 */, _mP/* s1kH9 */){
  return new T0(2);
},
_mQ/* $fReadInt_$sconvertInt */ = function(_mR/* s1vie */){
  var _mS/* s1vif */ = E(_mR/* s1vie */);
  if(_mS/* s1vif */._==5){
    var _mT/* s1vih */ = B(_mI/* Text.Read.Lex.numberToInteger */(_mS/* s1vif */.a));
    if(!_mT/* s1vih */._){
      return E(_mN/* Text.ParserCombinators.ReadPrec.pfail1 */);
    }else{
      var _mU/* s1vij */ = new T(function(){
        return B(_eJ/* GHC.Integer.Type.integerToInt */(_mT/* s1vih */.a));
      });
      return function(_mV/* s1vil */, _mW/* s1vim */){
        return new F(function(){return A1(_mW/* s1vim */,_mU/* s1vij */);});
      };
    }
  }else{
    return E(_mN/* Text.ParserCombinators.ReadPrec.pfail1 */);
  }
},
_mX/* readEither5 */ = function(_mY/* s2Rfe */){
  var _mZ/* s2Rfg */ = function(_n0/* s2Rfh */){
    return E(new T2(3,_mY/* s2Rfe */,_aY/* Text.ParserCombinators.ReadP.Fail */));
  };
  return new T1(1,function(_n1/* s2Rfi */){
    return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_n1/* s2Rfi */, _mZ/* s2Rfg */);});
  });
},
_n2/* updateElementValue1 */ = new T(function(){
  return B(A3(_mn/* GHC.Read.$fReadInt3 */,_mQ/* GHC.Read.$fReadInt_$sconvertInt */, _lS/* Text.ParserCombinators.ReadPrec.minPrec */, _mX/* Text.Read.readEither5 */));
}),
_n3/* updateElementValue */ = function(_n4/* sjeb */, _n5/* sjec */){
  var _n6/* sjed */ = E(_n4/* sjeb */);
  switch(_n6/* sjed */._){
    case 1:
      return new T3(1,_n6/* sjed */.a,_n5/* sjec */,_n6/* sjed */.c);
    case 2:
      return new T3(2,_n6/* sjed */.a,_n5/* sjec */,_n6/* sjed */.c);
    case 3:
      return new T3(3,_n6/* sjed */.a,_n5/* sjec */,_n6/* sjed */.c);
    case 4:
      return new T4(4,_n6/* sjed */.a,new T(function(){
        var _n7/* sjes */ = B(_8l/* Text.Read.readEither6 */(B(_8s/* Text.ParserCombinators.ReadP.run */(_n2/* FormEngine.FormElement.Updating.updateElementValue1 */, _n5/* sjec */))));
        if(!_n7/* sjes */._){
          return __Z/* EXTERNAL */;
        }else{
          if(!E(_n7/* sjes */.b)._){
            return new T1(1,_n7/* sjes */.a);
          }else{
            return __Z/* EXTERNAL */;
          }
        }
      }),_n6/* sjed */.c,_n6/* sjed */.d);
    case 6:
      var _n8/* sjeY */ = new T(function(){
        return B(_8H/* GHC.Base.map */(function(_n9/* sjeC */){
          var _na/* sjeD */ = E(_n9/* sjeC */);
          if(!_na/* sjeD */._){
            var _nb/* sjeG */ = E(_na/* sjeD */.a);
            return (_nb/* sjeG */._==0) ? (!B(_2n/* GHC.Base.eqString */(_nb/* sjeG */.a, _n5/* sjec */))) ? new T2(0,_nb/* sjeG */,_4x/* GHC.Types.False */) : new T2(0,_nb/* sjeG */,_8G/* GHC.Types.True */) : (!B(_2n/* GHC.Base.eqString */(_nb/* sjeG */.b, _n5/* sjec */))) ? new T2(0,_nb/* sjeG */,_4x/* GHC.Types.False */) : new T2(0,_nb/* sjeG */,_8G/* GHC.Types.True */);
          }else{
            var _nc/* sjeP */ = _na/* sjeD */.c,
            _nd/* sjeQ */ = E(_na/* sjeD */.a);
            return (_nd/* sjeQ */._==0) ? (!B(_2n/* GHC.Base.eqString */(_nd/* sjeQ */.a, _n5/* sjec */))) ? new T3(1,_nd/* sjeQ */,_4x/* GHC.Types.False */,_nc/* sjeP */) : new T3(1,_nd/* sjeQ */,_8G/* GHC.Types.True */,_nc/* sjeP */) : (!B(_2n/* GHC.Base.eqString */(_nd/* sjeQ */.b, _n5/* sjec */))) ? new T3(1,_nd/* sjeQ */,_4x/* GHC.Types.False */,_nc/* sjeP */) : new T3(1,_nd/* sjeQ */,_8G/* GHC.Types.True */,_nc/* sjeP */);
          }
        }, _n6/* sjed */.b));
      });
      return new T3(6,_n6/* sjed */.a,_n8/* sjeY */,_n6/* sjed */.c);
    case 7:
      return new T3(7,_n6/* sjed */.a,new T(function(){
        if(!B(_2n/* GHC.Base.eqString */(_n5/* sjec */, _k/* GHC.Types.[] */))){
          return new T1(1,_n5/* sjec */);
        }else{
          return __Z/* EXTERNAL */;
        }
      }),_n6/* sjed */.c);
    default:
      return E(_n6/* sjed */);
  }
},
_ne/* identity2elementUpdated2 */ = function(_nf/* sjf4 */, _/* EXTERNAL */){
  var _ng/* sjf6 */ = E(_nf/* sjf4 */);
  switch(_ng/* sjf6 */._){
    case 0:
      var _nh/* sjfn */ = B(_8D/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ng/* sjf6 */.a)).b)), _/* EXTERNAL */)),
      _ni/* sjfv */ = __app1/* EXTERNAL */(E(_8c/* FormEngine.JQuery.getRadioValue_f1 */), E(_nh/* sjfn */));
      return new T(function(){
        return B(_n3/* FormEngine.FormElement.Updating.updateElementValue */(_ng/* sjf6 */, new T(function(){
          var _nj/* sjfz */ = String/* EXTERNAL */(_ni/* sjfv */);
          return fromJSStr/* EXTERNAL */(_nj/* sjfz */);
        })));
      });
    case 1:
      var _nk/* sjfX */ = B(_8D/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ng/* sjf6 */.a)).b)), _/* EXTERNAL */)),
      _nl/* sjg5 */ = __app1/* EXTERNAL */(E(_8c/* FormEngine.JQuery.getRadioValue_f1 */), E(_nk/* sjfX */));
      return new T(function(){
        return B(_n3/* FormEngine.FormElement.Updating.updateElementValue */(_ng/* sjf6 */, new T(function(){
          var _nm/* sjg9 */ = String/* EXTERNAL */(_nl/* sjg5 */);
          return fromJSStr/* EXTERNAL */(_nm/* sjg9 */);
        })));
      });
    case 2:
      var _nn/* sjgx */ = B(_8D/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ng/* sjf6 */.a)).b)), _/* EXTERNAL */)),
      _no/* sjgF */ = __app1/* EXTERNAL */(E(_8c/* FormEngine.JQuery.getRadioValue_f1 */), E(_nn/* sjgx */));
      return new T(function(){
        return B(_n3/* FormEngine.FormElement.Updating.updateElementValue */(_ng/* sjf6 */, new T(function(){
          var _np/* sjgJ */ = String/* EXTERNAL */(_no/* sjgF */);
          return fromJSStr/* EXTERNAL */(_np/* sjgJ */);
        })));
      });
    case 3:
      var _nq/* sjh7 */ = B(_8D/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ng/* sjf6 */.a)).b)), _/* EXTERNAL */)),
      _nr/* sjhf */ = __app1/* EXTERNAL */(E(_8c/* FormEngine.JQuery.getRadioValue_f1 */), E(_nq/* sjh7 */));
      return new T(function(){
        return B(_n3/* FormEngine.FormElement.Updating.updateElementValue */(_ng/* sjf6 */, new T(function(){
          var _ns/* sjhj */ = String/* EXTERNAL */(_nr/* sjhf */);
          return fromJSStr/* EXTERNAL */(_ns/* sjhj */);
        })));
      });
    case 4:
      var _nt/* sjhr */ = _ng/* sjf6 */.a,
      _nu/* sjhu */ = _ng/* sjf6 */.d,
      _nv/* sjhx */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(_nt/* sjhr */)).b,
      _nw/* sjhI */ = B(_8D/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(_nv/* sjhx */)), _/* EXTERNAL */)),
      _nx/* sjhQ */ = __app1/* EXTERNAL */(E(_8c/* FormEngine.JQuery.getRadioValue_f1 */), E(_nw/* sjhI */)),
      _ny/* sjhV */ = B(_8d/* FormEngine.JQuery.getRadioValue1 */(new T(function(){
        return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(_nv/* sjhx */)), _8k/* FormEngine.FormItem.nfiUnitId1 */));
      },1), _/* EXTERNAL */));
      return new T(function(){
        var _nz/* sjhY */ = new T(function(){
          var _nA/* sji0 */ = String/* EXTERNAL */(_nx/* sjhQ */);
          return fromJSStr/* EXTERNAL */(_nA/* sji0 */);
        }),
        _nB/* sji6 */ = function(_nC/* sji7 */){
          return new T4(4,_nt/* sjhr */,new T(function(){
            var _nD/* sji9 */ = B(_8l/* Text.Read.readEither6 */(B(_8s/* Text.ParserCombinators.ReadP.run */(_n2/* FormEngine.FormElement.Updating.updateElementValue1 */, _nz/* sjhY */))));
            if(!_nD/* sji9 */._){
              return __Z/* EXTERNAL */;
            }else{
              if(!E(_nD/* sji9 */.b)._){
                return new T1(1,_nD/* sji9 */.a);
              }else{
                return __Z/* EXTERNAL */;
              }
            }
          }),_4y/* GHC.Base.Nothing */,_nu/* sjhu */);
        };
        if(!B(_2n/* GHC.Base.eqString */(_ny/* sjhV */, _8j/* FormEngine.FormElement.Updating.lvl2 */))){
          var _nE/* sjih */ = E(_ny/* sjhV */);
          if(!_nE/* sjih */._){
            return B(_nB/* sji6 */(_/* EXTERNAL */));
          }else{
            return new T4(4,_nt/* sjhr */,new T(function(){
              var _nF/* sjil */ = B(_8l/* Text.Read.readEither6 */(B(_8s/* Text.ParserCombinators.ReadP.run */(_n2/* FormEngine.FormElement.Updating.updateElementValue1 */, _nz/* sjhY */))));
              if(!_nF/* sjil */._){
                return __Z/* EXTERNAL */;
              }else{
                if(!E(_nF/* sjil */.b)._){
                  return new T1(1,_nF/* sjil */.a);
                }else{
                  return __Z/* EXTERNAL */;
                }
              }
            }),new T1(1,_nE/* sjih */),_nu/* sjhu */);
          }
        }else{
          return B(_nB/* sji6 */(_/* EXTERNAL */));
        }
      });
    case 5:
      var _nG/* sjiJ */ = B(_8D/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ng/* sjf6 */.a)).b)), _/* EXTERNAL */)),
      _nH/* sjiR */ = __app1/* EXTERNAL */(E(_8c/* FormEngine.JQuery.getRadioValue_f1 */), E(_nG/* sjiJ */));
      return new T(function(){
        return B(_n3/* FormEngine.FormElement.Updating.updateElementValue */(_ng/* sjf6 */, new T(function(){
          var _nI/* sjiV */ = String/* EXTERNAL */(_nH/* sjiR */);
          return fromJSStr/* EXTERNAL */(_nI/* sjiV */);
        })));
      });
    case 6:
      var _nJ/* sjjj */ = B(_8D/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ng/* sjf6 */.a)).b)), _/* EXTERNAL */)),
      _nK/* sjjr */ = __app1/* EXTERNAL */(E(_8c/* FormEngine.JQuery.getRadioValue_f1 */), E(_nJ/* sjjj */));
      return new T(function(){
        return B(_n3/* FormEngine.FormElement.Updating.updateElementValue */(_ng/* sjf6 */, new T(function(){
          var _nL/* sjjv */ = String/* EXTERNAL */(_nK/* sjjr */);
          return fromJSStr/* EXTERNAL */(_nL/* sjjv */);
        })));
      });
    case 7:
      var _nM/* sjjT */ = B(_8D/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ng/* sjf6 */.a)).b)), _/* EXTERNAL */)),
      _nN/* sjk1 */ = __app1/* EXTERNAL */(E(_8c/* FormEngine.JQuery.getRadioValue_f1 */), E(_nM/* sjjT */));
      return new T(function(){
        return B(_n3/* FormEngine.FormElement.Updating.updateElementValue */(_ng/* sjf6 */, new T(function(){
          var _nO/* sjk5 */ = String/* EXTERNAL */(_nN/* sjk1 */);
          return fromJSStr/* EXTERNAL */(_nO/* sjk5 */);
        })));
      });
    case 8:
      var _nP/* sjkt */ = B(_8D/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ng/* sjf6 */.a)).b)), _/* EXTERNAL */)),
      _nQ/* sjkB */ = __app1/* EXTERNAL */(E(_8c/* FormEngine.JQuery.getRadioValue_f1 */), E(_nP/* sjkt */));
      return new T(function(){
        return B(_n3/* FormEngine.FormElement.Updating.updateElementValue */(_ng/* sjf6 */, new T(function(){
          var _nR/* sjkF */ = String/* EXTERNAL */(_nQ/* sjkB */);
          return fromJSStr/* EXTERNAL */(_nR/* sjkF */);
        })));
      });
    case 9:
      var _nS/* sjl4 */ = B(_8D/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ng/* sjf6 */.a)).b)), _/* EXTERNAL */)),
      _nT/* sjlc */ = __app1/* EXTERNAL */(E(_8c/* FormEngine.JQuery.getRadioValue_f1 */), E(_nS/* sjl4 */));
      return new T(function(){
        return B(_n3/* FormEngine.FormElement.Updating.updateElementValue */(_ng/* sjf6 */, new T(function(){
          var _nU/* sjlg */ = String/* EXTERNAL */(_nT/* sjlc */);
          return fromJSStr/* EXTERNAL */(_nU/* sjlg */);
        })));
      });
    case 10:
      var _nV/* sjlE */ = B(_8D/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ng/* sjf6 */.a)).b)), _/* EXTERNAL */)),
      _nW/* sjlM */ = __app1/* EXTERNAL */(E(_8c/* FormEngine.JQuery.getRadioValue_f1 */), E(_nV/* sjlE */));
      return new T(function(){
        return B(_n3/* FormEngine.FormElement.Updating.updateElementValue */(_ng/* sjf6 */, new T(function(){
          var _nX/* sjlQ */ = String/* EXTERNAL */(_nW/* sjlM */);
          return fromJSStr/* EXTERNAL */(_nX/* sjlQ */);
        })));
      });
    case 11:
      var _nY/* sjmd */ = B(_8D/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ng/* sjf6 */.a)).b)), _/* EXTERNAL */)),
      _nZ/* sjml */ = __app1/* EXTERNAL */(E(_8c/* FormEngine.JQuery.getRadioValue_f1 */), E(_nY/* sjmd */));
      return new T(function(){
        return B(_n3/* FormEngine.FormElement.Updating.updateElementValue */(_ng/* sjf6 */, new T(function(){
          var _o0/* sjmp */ = String/* EXTERNAL */(_nZ/* sjml */);
          return fromJSStr/* EXTERNAL */(_o0/* sjmp */);
        })));
      });
    default:
      var _o1/* sjmM */ = B(_8D/* FormEngine.JQuery.selectByName1 */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ng/* sjf6 */.a)).b)), _/* EXTERNAL */)),
      _o2/* sjmU */ = __app1/* EXTERNAL */(E(_8c/* FormEngine.JQuery.getRadioValue_f1 */), E(_o1/* sjmM */));
      return new T(function(){
        return B(_n3/* FormEngine.FormElement.Updating.updateElementValue */(_ng/* sjf6 */, new T(function(){
          var _o3/* sjmY */ = String/* EXTERNAL */(_o2/* sjmU */);
          return fromJSStr/* EXTERNAL */(_o3/* sjmY */);
        })));
      });
  }
},
_o4/* identity2elementUpdated3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" does not exist"));
}),
_o5/* identity2elementUpdated4 */ = new T2(1,_5g/* GHC.Show.shows5 */,_k/* GHC.Types.[] */),
_o6/* $wa */ = function(_o7/* sjnH */, _o8/* sjnI */, _/* EXTERNAL */){
  var _o9/* sjnK */ = B(_80/* FormEngine.FormElement.Updating.identity2element' */(_o7/* sjnH */, _o8/* sjnI */));
  if(!_o9/* sjnK */._){
    var _oa/* sjnN */ = new T(function(){
      return B(_7/* GHC.Base.++ */(new T2(1,_5g/* GHC.Show.shows5 */,new T(function(){
        return B(_7j/* GHC.Show.showLitString */(_o7/* sjnH */, _o5/* FormEngine.FormElement.Updating.identity2elementUpdated4 */));
      })), _o4/* FormEngine.FormElement.Updating.identity2elementUpdated3 */));
    }),
    _ob/* sjnP */ = B(_3/* FormEngine.JQuery.errorIO1 */(B(unAppCStr/* EXTERNAL */("identity2elementUpdated: element with identity=", _oa/* sjnN */)), _/* EXTERNAL */));
    return _4y/* GHC.Base.Nothing */;
  }else{
    var _oc/* sjnT */ = B(_ne/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_o9/* sjnK */.a, _/* EXTERNAL */));
    return new T1(1,_oc/* sjnT */);
  }
},
_od/* setVal2 */ = "(function (val, jq) { jq.val(val).change(); return jq; })",
_oe/* $wa35 */ = function(_of/* slU3 */, _og/* slU4 */, _/* EXTERNAL */){
  var _oh/* slUe */ = eval/* EXTERNAL */(E(_od/* FormEngine.JQuery.setVal2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_oh/* slUe */), toJSStr/* EXTERNAL */(E(_of/* slU3 */)), _og/* slU4 */);});
},
_oi/* $fExceptionRecSelError_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RecSelError"));
}),
_oj/* $fExceptionRecSelError_wild */ = new T5(0,new Long/* EXTERNAL */(2975920724, 3651309139, true),new Long/* EXTERNAL */(465443624, 4160253997, true),_8L/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_8M/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_oi/* Control.Exception.Base.$fExceptionRecSelError_ww4 */),
_ok/* $fExceptionRecSelError2 */ = new T5(0,new Long/* EXTERNAL */(2975920724, 3651309139, true),new Long/* EXTERNAL */(465443624, 4160253997, true),_oj/* Control.Exception.Base.$fExceptionRecSelError_wild */,_k/* GHC.Types.[] */,_k/* GHC.Types.[] */),
_ol/* $fExceptionRecSelError1 */ = function(_om/* s4nv0 */){
  return E(_ok/* Control.Exception.Base.$fExceptionRecSelError2 */);
},
_on/* $fExceptionRecSelError_$cfromException */ = function(_oo/* s4nvr */){
  var _op/* s4nvs */ = E(_oo/* s4nvr */);
  return new F(function(){return _8U/* Data.Typeable.cast */(B(_8S/* GHC.Exception.$p1Exception */(_op/* s4nvs */.a)), _ol/* Control.Exception.Base.$fExceptionRecSelError1 */, _op/* s4nvs */.b);});
},
_oq/* $fExceptionRecSelError_$cshow */ = function(_or/* s4nvj */){
  return E(E(_or/* s4nvj */).a);
},
_os/* $fExceptionRecSelError_$ctoException */ = function(_98/* B1 */){
  return new T2(0,_ot/* Control.Exception.Base.$fExceptionRecSelError */,_98/* B1 */);
},
_ou/* $fShowRecSelError1 */ = function(_ov/* s4nqO */, _ow/* s4nqP */){
  return new F(function(){return _7/* GHC.Base.++ */(E(_ov/* s4nqO */).a, _ow/* s4nqP */);});
},
_ox/* $fShowRecSelError_$cshowList */ = function(_oy/* s4nvh */, _oz/* s4nvi */){
  return new F(function(){return _5t/* GHC.Show.showList__ */(_ou/* Control.Exception.Base.$fShowRecSelError1 */, _oy/* s4nvh */, _oz/* s4nvi */);});
},
_oA/* $fShowRecSelError_$cshowsPrec */ = function(_oB/* s4nvm */, _oC/* s4nvn */, _oD/* s4nvo */){
  return new F(function(){return _7/* GHC.Base.++ */(E(_oC/* s4nvn */).a, _oD/* s4nvo */);});
},
_oE/* $fShowRecSelError */ = new T3(0,_oA/* Control.Exception.Base.$fShowRecSelError_$cshowsPrec */,_oq/* Control.Exception.Base.$fExceptionRecSelError_$cshow */,_ox/* Control.Exception.Base.$fShowRecSelError_$cshowList */),
_ot/* $fExceptionRecSelError */ = new T(function(){
  return new T5(0,_ol/* Control.Exception.Base.$fExceptionRecSelError1 */,_oE/* Control.Exception.Base.$fShowRecSelError */,_os/* Control.Exception.Base.$fExceptionRecSelError_$ctoException */,_on/* Control.Exception.Base.$fExceptionRecSelError_$cfromException */,_oq/* Control.Exception.Base.$fExceptionRecSelError_$cshow */);
}),
_oF/* recSelError */ = function(_oG/* s4nwW */){
  var _oH/* s4nwY */ = new T(function(){
    return B(unAppCStr/* EXTERNAL */("No match in record selector ", new T(function(){
      return B(unCStr/* EXTERNAL */(_oG/* s4nwW */));
    })));
  });
  return new F(function(){return _9r/* GHC.Exception.throw1 */(new T1(0,_oH/* s4nwY */), _ot/* Control.Exception.Base.$fExceptionRecSelError */);});
},
_oI/* neMaybeValue1 */ = new T(function(){
  return B(_oF/* Control.Exception.Base.recSelError */("neMaybeValue"));
}),
_oJ/* $wgo */ = function(_oK/* sjoa */, _oL/* sjob */){
  while(1){
    var _oM/* sjoc */ = E(_oK/* sjoa */);
    if(!_oM/* sjoc */._){
      return E(_oL/* sjob */);
    }else{
      var _oN/* sjoe */ = _oM/* sjoc */.b,
      _oO/* sjof */ = E(_oM/* sjoc */.a);
      if(_oO/* sjof */._==4){
        var _oP/* sjol */ = E(_oO/* sjof */.b);
        if(!_oP/* sjol */._){
          _oK/* sjoa */ = _oN/* sjoe */;
          continue;
        }else{
          var _oQ/*  sjob */ = _oL/* sjob */+E(_oP/* sjol */.a)|0;
          _oK/* sjoa */ = _oN/* sjoe */;
          _oL/* sjob */ = _oQ/*  sjob */;
          continue;
        }
      }else{
        return E(_oI/* FormEngine.FormElement.FormElement.neMaybeValue1 */);
      }
    }
  }
},
_oR/* int2Float */ = function(_oS/* sc58 */){
  return E(_oS/* sc58 */);
},
_oT/* numberElem2TB1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_oU/* numberElem2TB2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_oV/* numberElem2TB3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_oW/* numberElem2TB4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_oX/* numberElem2TB */ = function(_oY/* scjR */){
  var _oZ/* scjS */ = E(_oY/* scjR */);
  if(_oZ/* scjS */._==4){
    var _p0/* scjU */ = _oZ/* scjS */.b,
    _p1/* scjX */ = E(_oZ/* scjS */.c);
    if(!_p1/* scjX */._){
      return __Z/* EXTERNAL */;
    }else{
      var _p2/* scjY */ = _p1/* scjX */.a;
      if(!B(_2n/* GHC.Base.eqString */(_p2/* scjY */, _oW/* FormEngine.FormElement.FormElement.numberElem2TB4 */))){
        if(!B(_2n/* GHC.Base.eqString */(_p2/* scjY */, _oV/* FormEngine.FormElement.FormElement.numberElem2TB3 */))){
          if(!B(_2n/* GHC.Base.eqString */(_p2/* scjY */, _oU/* FormEngine.FormElement.FormElement.numberElem2TB2 */))){
            if(!B(_2n/* GHC.Base.eqString */(_p2/* scjY */, _oT/* FormEngine.FormElement.FormElement.numberElem2TB1 */))){
              return __Z/* EXTERNAL */;
            }else{
              var _p3/* sck3 */ = E(_p0/* scjU */);
              return (_p3/* sck3 */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
                return B(_oR/* GHC.Float.RealFracMethods.int2Float */(_p3/* sck3 */.a));
              }));
            }
          }else{
            var _p4/* sck6 */ = E(_p0/* scjU */);
            return (_p4/* sck6 */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
              return E(_p4/* sck6 */.a)*1000;
            }));
          }
        }else{
          var _p5/* sckd */ = E(_p0/* scjU */);
          return (_p5/* sckd */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
            return E(_p5/* sckd */.a)*1.0e-6;
          }));
        }
      }else{
        var _p6/* sckk */ = E(_p0/* scjU */);
        return (_p6/* sckk */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
          return E(_p6/* sckk */.a)*1.0e-3;
        }));
      }
    }
  }else{
    return __Z/* EXTERNAL */;
  }
},
_p7/* $wgo1 */ = function(_p8/* sjow */, _p9/* sjox */){
  while(1){
    var _pa/* sjoy */ = E(_p8/* sjow */);
    if(!_pa/* sjoy */._){
      return E(_p9/* sjox */);
    }else{
      var _pb/* sjoA */ = _pa/* sjoy */.b,
      _pc/* sjoB */ = B(_oX/* FormEngine.FormElement.FormElement.numberElem2TB */(_pa/* sjoy */.a));
      if(!_pc/* sjoB */._){
        _p8/* sjow */ = _pb/* sjoA */;
        continue;
      }else{
        var _pd/*  sjox */ = _p9/* sjox */+E(_pc/* sjoB */.a);
        _p8/* sjow */ = _pb/* sjoA */;
        _p9/* sjox */ = _pd/*  sjox */;
        continue;
      }
    }
  }
},
_pe/* catMaybes1 */ = function(_pf/*  s7rA */){
  while(1){
    var _pg/*  catMaybes1 */ = B((function(_ph/* s7rA */){
      var _pi/* s7rB */ = E(_ph/* s7rA */);
      if(!_pi/* s7rB */._){
        return __Z/* EXTERNAL */;
      }else{
        var _pj/* s7rD */ = _pi/* s7rB */.b,
        _pk/* s7rE */ = E(_pi/* s7rB */.a);
        if(!_pk/* s7rE */._){
          _pf/*  s7rA */ = _pj/* s7rD */;
          return __continue/* EXTERNAL */;
        }else{
          return new T2(1,_pk/* s7rE */.a,new T(function(){
            return B(_pe/* Data.Maybe.catMaybes1 */(_pj/* s7rD */));
          }));
        }
      }
    })(_pf/*  s7rA */));
    if(_pg/*  catMaybes1 */!=__continue/* EXTERNAL */){
      return _pg/*  catMaybes1 */;
    }
  }
},
_pl/* disableJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("true"));
}),
_pm/* disableJq3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("readonly"));
}),
_pn/* disableJq6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#eee"));
}),
_po/* disableJq7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("background-color"));
}),
_pp/* elementId */ = function(_pq/* sc3G */){
  return new F(function(){return _27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_pq/* sc3G */)))).b);});
},
_pr/* go */ = function(_ps/* sjo4 */){
  while(1){
    var _pt/* sjo5 */ = E(_ps/* sjo4 */);
    if(!_pt/* sjo5 */._){
      return false;
    }else{
      if(!E(_pt/* sjo5 */.a)._){
        return true;
      }else{
        _ps/* sjo4 */ = _pt/* sjo5 */.b;
        continue;
      }
    }
  }
},
_pu/* go1 */ = function(_pv/* sjoq */){
  while(1){
    var _pw/* sjor */ = E(_pv/* sjoq */);
    if(!_pw/* sjor */._){
      return false;
    }else{
      if(!E(_pw/* sjor */.a)._){
        return true;
      }else{
        _pv/* sjoq */ = _pw/* sjor */.b;
        continue;
      }
    }
  }
},
_px/* selectIn2 */ = "(function (elId, context) { return $(elId, context); })",
_py/* $wa18 */ = function(_pz/* slXx */, _pA/* slXy */, _/* EXTERNAL */){
  var _pB/* slXI */ = eval/* EXTERNAL */(E(_px/* FormEngine.JQuery.selectIn2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_pB/* slXI */), toJSStr/* EXTERNAL */(E(_pz/* slXx */)), _pA/* slXy */);});
},
_pC/* flagPlaceId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_flagPlaceId"));
}),
_pD/* flagPlaceId */ = function(_pE/* sfOe */){
  return new F(function(){return _7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_pE/* sfOe */)))).b)), _pC/* FormEngine.FormElement.Identifiers.flagPlaceId1 */);});
},
_pF/* inputFieldUpdate3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".validity-flag"));
}),
_pG/* inputFieldUpdate4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_pH/* invalidImg */ = function(_pI/* seuC */){
  return E(E(_pI/* seuC */).c);
},
_pJ/* removeJq_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { var p = jq.parent(); jq.remove(); return p; })");
}),
_pK/* validImg */ = function(_pL/* seuH */){
  return E(E(_pL/* seuH */).b);
},
_pM/* inputFieldUpdate2 */ = function(_pN/* sjde */, _pO/* sjdf */, _pP/* sjdg */, _/* EXTERNAL */){
  var _pQ/* sjdk */ = B(_2E/* FormEngine.JQuery.select1 */(B(_7/* GHC.Base.++ */(_pG/* FormEngine.FormElement.Updating.inputFieldUpdate4 */, new T(function(){
    return B(_pD/* FormEngine.FormElement.Identifiers.flagPlaceId */(_pN/* sjde */));
  },1))), _/* EXTERNAL */)),
  _pR/* sjdn */ = E(_pQ/* sjdk */),
  _pS/* sjdp */ = B(_py/* FormEngine.JQuery.$wa18 */(_pF/* FormEngine.FormElement.Updating.inputFieldUpdate3 */, _pR/* sjdn */, _/* EXTERNAL */)),
  _pT/* sjdx */ = __app1/* EXTERNAL */(E(_pJ/* FormEngine.JQuery.removeJq_f1 */), E(_pS/* sjdp */));
  if(!E(_pP/* sjdg */)){
    if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_pN/* sjde */)))).j)){
      return _0/* GHC.Tuple.() */;
    }else{
      var _pU/* sjdQ */ = B(_X/* FormEngine.JQuery.$wa3 */(B(_pH/* FormEngine.FormContext.invalidImg */(_pO/* sjdf */)), _pR/* sjdn */, _/* EXTERNAL */));
      return _0/* GHC.Tuple.() */;
    }
  }else{
    if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_pN/* sjde */)))).j)){
      return _0/* GHC.Tuple.() */;
    }else{
      var _pV/* sje8 */ = B(_X/* FormEngine.JQuery.$wa3 */(B(_pK/* FormEngine.FormContext.validImg */(_pO/* sjdf */)), _pR/* sjdn */, _/* EXTERNAL */));
      return _0/* GHC.Tuple.() */;
    }
  }
},
_pW/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rule application did not unify: "));
}),
_pX/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" @"));
}),
_pY/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("invalid operand in "));
}),
_pZ/* selectByIdentity2 */ = "(function (identity) { return $(\'[identity=\"\' + identity + \'\"]\'); })",
_q0/* selectByIdentity1 */ = function(_q1/* slKc */, _/* EXTERNAL */){
  var _q2/* slKm */ = eval/* EXTERNAL */(E(_pZ/* FormEngine.JQuery.selectByIdentity2 */));
  return new F(function(){return __app1/* EXTERNAL */(E(_q2/* slKm */), toJSStr/* EXTERNAL */(E(_q1/* slKc */)));});
},
_q3/* applyRule1 */ = function(_q4/* sjoG */, _q5/* sjoH */, _q6/* sjoI */, _/* EXTERNAL */){
  var _q7/* sjoK */ = function(_/* EXTERNAL */){
    var _q8/* sjoM */ = E(_q6/* sjoI */);
    switch(_q8/* sjoM */._){
      case 2:
        var _q9/* sjoU */ = B(_q0/* FormEngine.JQuery.selectByIdentity1 */(_q8/* sjoM */.a, _/* EXTERNAL */)),
        _qa/* sjp2 */ = __app1/* EXTERNAL */(E(_8c/* FormEngine.JQuery.getRadioValue_f1 */), E(_q9/* sjoU */)),
        _qb/* sjp5 */ = B(_q0/* FormEngine.JQuery.selectByIdentity1 */(_q8/* sjoM */.b, _/* EXTERNAL */)),
        _qc/* sjp9 */ = String/* EXTERNAL */(_qa/* sjp2 */),
        _qd/* sjpi */ = B(_oe/* FormEngine.JQuery.$wa35 */(fromJSStr/* EXTERNAL */(_qc/* sjp9 */), E(_qb/* sjp5 */), _/* EXTERNAL */));
        return _0/* GHC.Tuple.() */;
      case 3:
        var _qe/* sjpm */ = B(_8D/* FormEngine.JQuery.selectByName1 */(B(_pp/* FormEngine.FormElement.FormElement.elementId */(_q4/* sjoG */)), _/* EXTERNAL */)),
        _qf/* sjpp */ = E(_qe/* sjpm */),
        _qg/* sjpr */ = B(_K/* FormEngine.JQuery.$wa2 */(_po/* FormEngine.JQuery.disableJq7 */, _pn/* FormEngine.JQuery.disableJq6 */, _qf/* sjpp */, _/* EXTERNAL */)),
        _qh/* sjpu */ = B(_u/* FormEngine.JQuery.$wa6 */(_pm/* FormEngine.JQuery.disableJq3 */, _pl/* FormEngine.JQuery.disableJq2 */, _qf/* sjpp */, _/* EXTERNAL */));
        return _0/* GHC.Tuple.() */;
      case 4:
        var _qi/* sjpy */ = B(_ne/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_q4/* sjoG */, _/* EXTERNAL */)),
        _qj/* sjpB */ = E(_qi/* sjpy */);
        if(_qj/* sjpB */._==4){
          var _qk/* sjpH */ = E(_qj/* sjpB */.b);
          if(!_qk/* sjpH */._){
            return new F(function(){return _pM/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_qj/* sjpB */, _q5/* sjoH */, _4x/* GHC.Types.False */, _/* EXTERNAL */);});
          }else{
            return new F(function(){return _pM/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_qj/* sjpB */, _q5/* sjoH */, new T(function(){
              return B(A1(_q8/* sjoM */.a,_qk/* sjpH */.a));
            },1), _/* EXTERNAL */);});
          }
        }else{
          return E(_oI/* FormEngine.FormElement.FormElement.neMaybeValue1 */);
        }
        break;
      default:
        var _ql/* sjoQ */ = new T(function(){
          var _qm/* sjoP */ = new T(function(){
            return B(_7/* GHC.Base.++ */(_pX/* FormEngine.FormElement.Updating.lvl4 */, new T(function(){
              return B(_55/* FormEngine.FormElement.FormElement.$fShowFormElement_$cshow */(_q4/* sjoG */));
            },1)));
          },1);
          return B(_7/* GHC.Base.++ */(B(_7R/* FormEngine.FormItem.$fShowFormRule_$cshow */(_q8/* sjoM */)), _qm/* sjoP */));
        },1);
        return new F(function(){return _3/* FormEngine.JQuery.errorIO1 */(B(_7/* GHC.Base.++ */(_pW/* FormEngine.FormElement.Updating.lvl3 */, _ql/* sjoQ */)), _/* EXTERNAL */);});
    }
  };
  if(E(_q4/* sjoG */)._==4){
    var _qn/* sjpP */ = E(_q6/* sjoI */);
    switch(_qn/* sjpP */._){
      case 0:
        var _qo/* sjpS */ = function(_/* EXTERNAL */, _qp/* sjpU */){
          if(!B(_pr/* FormEngine.FormElement.Updating.go */(_qp/* sjpU */))){
            var _qq/* sjpW */ = B(_q0/* FormEngine.JQuery.selectByIdentity1 */(_qn/* sjpP */.b, _/* EXTERNAL */)),
            _qr/* sjq4 */ = B(_oe/* FormEngine.JQuery.$wa35 */(B(_1M/* GHC.Show.$wshowSignedInt */(0, B(_oJ/* FormEngine.FormElement.Updating.$wgo */(B(_pe/* Data.Maybe.catMaybes1 */(_qp/* sjpU */)), 0)), _k/* GHC.Types.[] */)), E(_qq/* sjpW */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }else{
            var _qs/* sjq9 */ = B(_3/* FormEngine.JQuery.errorIO1 */(B(_7/* GHC.Base.++ */(_pY/* FormEngine.FormElement.Updating.lvl5 */, new T(function(){
              return B(_7R/* FormEngine.FormItem.$fShowFormRule_$cshow */(_qn/* sjpP */));
            },1))), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }
        },
        _qt/* sjqc */ = E(_qn/* sjpP */.a);
        if(!_qt/* sjqc */._){
          return new F(function(){return _qo/* sjpS */(_/* EXTERNAL */, _k/* GHC.Types.[] */);});
        }else{
          var _qu/* sjqg */ = E(_q5/* sjoH */).a,
          _qv/* sjqj */ = B(_o6/* FormEngine.FormElement.Updating.$wa */(_qt/* sjqc */.a, _qu/* sjqg */, _/* EXTERNAL */)),
          _qw/* sjqm */ = function(_qx/* sjqn */, _/* EXTERNAL */){
            var _qy/* sjqp */ = E(_qx/* sjqn */);
            if(!_qy/* sjqp */._){
              return _k/* GHC.Types.[] */;
            }else{
              var _qz/* sjqs */ = B(_o6/* FormEngine.FormElement.Updating.$wa */(_qy/* sjqp */.a, _qu/* sjqg */, _/* EXTERNAL */)),
              _qA/* sjqv */ = B(_qw/* sjqm */(_qy/* sjqp */.b, _/* EXTERNAL */));
              return new T2(1,_qz/* sjqs */,_qA/* sjqv */);
            }
          },
          _qB/* sjqz */ = B(_qw/* sjqm */(_qt/* sjqc */.b, _/* EXTERNAL */));
          return new F(function(){return _qo/* sjpS */(_/* EXTERNAL */, new T2(1,_qv/* sjqj */,_qB/* sjqz */));});
        }
        break;
      case 1:
        var _qC/* sjqF */ = function(_/* EXTERNAL */, _qD/* sjqH */){
          if(!B(_pu/* FormEngine.FormElement.Updating.go1 */(_qD/* sjqH */))){
            var _qE/* sjqJ */ = B(_q0/* FormEngine.JQuery.selectByIdentity1 */(_qn/* sjpP */.b, _/* EXTERNAL */)),
            _qF/* sjqP */ = jsShow/* EXTERNAL */(B(_p7/* FormEngine.FormElement.Updating.$wgo1 */(B(_pe/* Data.Maybe.catMaybes1 */(_qD/* sjqH */)), 0))),
            _qG/* sjqW */ = B(_oe/* FormEngine.JQuery.$wa35 */(fromJSStr/* EXTERNAL */(_qF/* sjqP */), E(_qE/* sjqJ */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }else{
            return _0/* GHC.Tuple.() */;
          }
        },
        _qH/* sjqZ */ = E(_qn/* sjpP */.a);
        if(!_qH/* sjqZ */._){
          return new F(function(){return _qC/* sjqF */(_/* EXTERNAL */, _k/* GHC.Types.[] */);});
        }else{
          var _qI/* sjr3 */ = E(_q5/* sjoH */).a,
          _qJ/* sjr6 */ = B(_o6/* FormEngine.FormElement.Updating.$wa */(_qH/* sjqZ */.a, _qI/* sjr3 */, _/* EXTERNAL */)),
          _qK/* sjr9 */ = function(_qL/* sjra */, _/* EXTERNAL */){
            var _qM/* sjrc */ = E(_qL/* sjra */);
            if(!_qM/* sjrc */._){
              return _k/* GHC.Types.[] */;
            }else{
              var _qN/* sjrf */ = B(_o6/* FormEngine.FormElement.Updating.$wa */(_qM/* sjrc */.a, _qI/* sjr3 */, _/* EXTERNAL */)),
              _qO/* sjri */ = B(_qK/* sjr9 */(_qM/* sjrc */.b, _/* EXTERNAL */));
              return new T2(1,_qN/* sjrf */,_qO/* sjri */);
            }
          },
          _qP/* sjrm */ = B(_qK/* sjr9 */(_qH/* sjqZ */.b, _/* EXTERNAL */));
          return new F(function(){return _qC/* sjqF */(_/* EXTERNAL */, new T2(1,_qJ/* sjr6 */,_qP/* sjrm */));});
        }
        break;
      default:
        return new F(function(){return _q7/* sjoK */(_/* EXTERNAL */);});
    }
  }else{
    return new F(function(){return _q7/* sjoK */(_/* EXTERNAL */);});
  }
},
_qQ/* applyRules1 */ = function(_qR/* sjrq */, _qS/* sjrr */, _/* EXTERNAL */){
  var _qT/* sjrG */ = function(_qU/* sjrH */, _/* EXTERNAL */){
    while(1){
      var _qV/* sjrJ */ = E(_qU/* sjrH */);
      if(!_qV/* sjrJ */._){
        return _0/* GHC.Tuple.() */;
      }else{
        var _qW/* sjrM */ = B(_q3/* FormEngine.FormElement.Updating.applyRule1 */(_qR/* sjrq */, _qS/* sjrr */, _qV/* sjrJ */.a, _/* EXTERNAL */));
        _qU/* sjrH */ = _qV/* sjrJ */.b;
        continue;
      }
    }
  };
  return new F(function(){return _qT/* sjrG */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_qR/* sjrq */)))).k, _/* EXTERNAL */);});
},
_qX/* isJust */ = function(_qY/* s7rZ */){
  return (E(_qY/* s7rZ */)._==0) ? false : true;
},
_qZ/* nfiUnit1 */ = new T(function(){
  return B(_oF/* Control.Exception.Base.recSelError */("nfiUnit"));
}),
_r0/* go */ = function(_r1/* seVC */){
  while(1){
    var _r2/* seVD */ = E(_r1/* seVC */);
    if(!_r2/* seVD */._){
      return true;
    }else{
      if(!E(_r2/* seVD */.a)){
        return false;
      }else{
        _r1/* seVC */ = _r2/* seVD */.b;
        continue;
      }
    }
  }
},
_r3/* validateElement_go */ = function(_r4/* seVl */){
  while(1){
    var _r5/* seVm */ = E(_r4/* seVl */);
    if(!_r5/* seVm */._){
      return false;
    }else{
      var _r6/* seVo */ = _r5/* seVm */.b,
      _r7/* seVp */ = E(_r5/* seVm */.a);
      if(!_r7/* seVp */._){
        if(!E(_r7/* seVp */.b)){
          _r4/* seVl */ = _r6/* seVo */;
          continue;
        }else{
          return true;
        }
      }else{
        if(!E(_r7/* seVp */.b)){
          _r4/* seVl */ = _r6/* seVo */;
          continue;
        }else{
          return true;
        }
      }
    }
  }
},
_r8/* validateElement_go1 */ = function(_r9/* seVx */){
  while(1){
    var _ra/* seVy */ = E(_r9/* seVx */);
    if(!_ra/* seVy */._){
      return true;
    }else{
      if(!E(_ra/* seVy */.a)){
        return false;
      }else{
        _r9/* seVx */ = _ra/* seVy */.b;
        continue;
      }
    }
  }
},
_rb/* go1 */ = function(_rc/*  seVO */){
  while(1){
    var _rd/*  go1 */ = B((function(_re/* seVO */){
      var _rf/* seVP */ = E(_re/* seVO */);
      if(!_rf/* seVP */._){
        return __Z/* EXTERNAL */;
      }else{
        var _rg/* seVR */ = _rf/* seVP */.b,
        _rh/* seVS */ = E(_rf/* seVP */.a);
        switch(_rh/* seVS */._){
          case 0:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rh/* seVS */.a)).j)){
              _rc/*  seVO */ = _rg/* seVR */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_ri/* FormEngine.FormElement.Validation.validateElement2 */(_rh/* seVS */.b));
              }),new T(function(){
                return B(_rb/* FormEngine.FormElement.Validation.go1 */(_rg/* seVR */));
              }));
            }
            break;
          case 1:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rh/* seVS */.a)).j)){
              _rc/*  seVO */ = _rg/* seVR */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!B(_aE/* GHC.Classes.$fEq[]_$s$c==1 */(_rh/* seVS */.b, _k/* GHC.Types.[] */))){
                  return true;
                }else{
                  return false;
                }
              }),new T(function(){
                return B(_rb/* FormEngine.FormElement.Validation.go1 */(_rg/* seVR */));
              }));
            }
            break;
          case 2:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rh/* seVS */.a)).j)){
              _rc/*  seVO */ = _rg/* seVR */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!B(_aE/* GHC.Classes.$fEq[]_$s$c==1 */(_rh/* seVS */.b, _k/* GHC.Types.[] */))){
                  return true;
                }else{
                  return false;
                }
              }),new T(function(){
                return B(_rb/* FormEngine.FormElement.Validation.go1 */(_rg/* seVR */));
              }));
            }
            break;
          case 3:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rh/* seVS */.a)).j)){
              _rc/*  seVO */ = _rg/* seVR */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!B(_aE/* GHC.Classes.$fEq[]_$s$c==1 */(_rh/* seVS */.b, _k/* GHC.Types.[] */))){
                  return true;
                }else{
                  return false;
                }
              }),new T(function(){
                return B(_rb/* FormEngine.FormElement.Validation.go1 */(_rg/* seVR */));
              }));
            }
            break;
          case 4:
            var _rj/* seX6 */ = _rh/* seVS */.a;
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rj/* seX6 */)).j)){
              _rc/*  seVO */ = _rg/* seVR */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                var _rk/* seXn */ = E(_rh/* seVS */.b);
                if(!_rk/* seXn */._){
                  return false;
                }else{
                  if(E(_rk/* seXn */.a)<0){
                    return false;
                  }else{
                    var _rl/* seXt */ = E(_rj/* seX6 */);
                    if(_rl/* seXt */._==3){
                      if(E(_rl/* seXt */.b)._==1){
                        return B(_qX/* Data.Maybe.isJust */(_rh/* seVS */.c));
                      }else{
                        return true;
                      }
                    }else{
                      return E(_qZ/* FormEngine.FormItem.nfiUnit1 */);
                    }
                  }
                }
              }),new T(function(){
                return B(_rb/* FormEngine.FormElement.Validation.go1 */(_rg/* seVR */));
              }));
            }
            break;
          case 5:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rh/* seVS */.a)).j)){
              _rc/*  seVO */ = _rg/* seVR */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,_8G/* GHC.Types.True */,new T(function(){
                return B(_rb/* FormEngine.FormElement.Validation.go1 */(_rg/* seVR */));
              }));
            }
            break;
          case 6:
            var _rm/* seXR */ = _rh/* seVS */.a,
            _rn/* seXS */ = _rh/* seVS */.b;
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rm/* seXR */)).j)){
              _rc/*  seVO */ = _rg/* seVR */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rm/* seXR */)).j)){
                  return B(_r8/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_8H/* GHC.Base.map */(_ro/* FormEngine.FormElement.Validation.validateElement1 */, _rn/* seXS */))));
                }else{
                  if(!B(_r3/* FormEngine.FormElement.Validation.validateElement_go */(_rn/* seXS */))){
                    return false;
                  }else{
                    return B(_r8/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_8H/* GHC.Base.map */(_ro/* FormEngine.FormElement.Validation.validateElement1 */, _rn/* seXS */))));
                  }
                }
              }),new T(function(){
                return B(_rb/* FormEngine.FormElement.Validation.go1 */(_rg/* seVR */));
              }));
            }
            break;
          case 7:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rh/* seVS */.a)).j)){
              _rc/*  seVO */ = _rg/* seVR */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_qX/* Data.Maybe.isJust */(_rh/* seVS */.b));
              }),new T(function(){
                return B(_rb/* FormEngine.FormElement.Validation.go1 */(_rg/* seVR */));
              }));
            }
            break;
          case 8:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rh/* seVS */.a)).j)){
              _rc/*  seVO */ = _rg/* seVR */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_ri/* FormEngine.FormElement.Validation.validateElement2 */(_rh/* seVS */.b));
              }),new T(function(){
                return B(_rb/* FormEngine.FormElement.Validation.go1 */(_rg/* seVR */));
              }));
            }
            break;
          case 9:
            return new T2(1,new T(function(){
              if(!E(_rh/* seVS */.b)){
                return true;
              }else{
                return B(_ri/* FormEngine.FormElement.Validation.validateElement2 */(_rh/* seVS */.c));
              }
            }),new T(function(){
              return B(_rb/* FormEngine.FormElement.Validation.go1 */(_rg/* seVR */));
            }));
          case 10:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rh/* seVS */.a)).j)){
              _rc/*  seVO */ = _rg/* seVR */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_ri/* FormEngine.FormElement.Validation.validateElement2 */(_rh/* seVS */.b));
              }),new T(function(){
                return B(_rb/* FormEngine.FormElement.Validation.go1 */(_rg/* seVR */));
              }));
            }
            break;
          case 11:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rh/* seVS */.a)).j)){
              _rc/*  seVO */ = _rg/* seVR */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,_8G/* GHC.Types.True */,new T(function(){
                return B(_rb/* FormEngine.FormElement.Validation.go1 */(_rg/* seVR */));
              }));
            }
            break;
          default:
            if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_rh/* seVS */.a)).j)){
              _rc/*  seVO */ = _rg/* seVR */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,_8G/* GHC.Types.True */,new T(function(){
                return B(_rb/* FormEngine.FormElement.Validation.go1 */(_rg/* seVR */));
              }));
            }
        }
      }
    })(_rc/*  seVO */));
    if(_rd/*  go1 */!=__continue/* EXTERNAL */){
      return _rd/*  go1 */;
    }
  }
},
_ri/* validateElement2 */ = function(_rp/* seZU */){
  return new F(function(){return _r0/* FormEngine.FormElement.Validation.go */(B(_rb/* FormEngine.FormElement.Validation.go1 */(_rp/* seZU */)));});
},
_ro/* validateElement1 */ = function(_rq/* seVH */){
  var _rr/* seVI */ = E(_rq/* seVH */);
  if(!_rr/* seVI */._){
    return true;
  }else{
    return new F(function(){return _ri/* FormEngine.FormElement.Validation.validateElement2 */(_rr/* seVI */.c);});
  }
},
_rs/* validateElement */ = function(_rt/* seZW */){
  var _ru/* seZX */ = E(_rt/* seZW */);
  switch(_ru/* seZX */._){
    case 0:
      return new F(function(){return _ri/* FormEngine.FormElement.Validation.validateElement2 */(_ru/* seZX */.b);});
      break;
    case 1:
      return (!B(_aE/* GHC.Classes.$fEq[]_$s$c==1 */(_ru/* seZX */.b, _k/* GHC.Types.[] */))) ? true : false;
    case 2:
      return (!B(_aE/* GHC.Classes.$fEq[]_$s$c==1 */(_ru/* seZX */.b, _k/* GHC.Types.[] */))) ? true : false;
    case 3:
      return (!B(_aE/* GHC.Classes.$fEq[]_$s$c==1 */(_ru/* seZX */.b, _k/* GHC.Types.[] */))) ? true : false;
    case 4:
      var _rv/* sf0h */ = E(_ru/* seZX */.b);
      if(!_rv/* sf0h */._){
        return false;
      }else{
        if(E(_rv/* sf0h */.a)<0){
          return false;
        }else{
          var _rw/* sf0n */ = E(_ru/* seZX */.a);
          if(_rw/* sf0n */._==3){
            if(E(_rw/* sf0n */.b)._==1){
              return new F(function(){return _qX/* Data.Maybe.isJust */(_ru/* seZX */.c);});
            }else{
              return true;
            }
          }else{
            return E(_qZ/* FormEngine.FormItem.nfiUnit1 */);
          }
        }
      }
      break;
    case 6:
      var _rx/* sf0u */ = _ru/* seZX */.b;
      if(!E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ru/* seZX */.a)).j)){
        return new F(function(){return _r8/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_8H/* GHC.Base.map */(_ro/* FormEngine.FormElement.Validation.validateElement1 */, _rx/* sf0u */)));});
      }else{
        if(!B(_r3/* FormEngine.FormElement.Validation.validateElement_go */(_rx/* sf0u */))){
          return false;
        }else{
          return new F(function(){return _r8/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_8H/* GHC.Base.map */(_ro/* FormEngine.FormElement.Validation.validateElement1 */, _rx/* sf0u */)));});
        }
      }
      break;
    case 7:
      return new F(function(){return _qX/* Data.Maybe.isJust */(_ru/* seZX */.b);});
      break;
    case 8:
      return new F(function(){return _ri/* FormEngine.FormElement.Validation.validateElement2 */(_ru/* seZX */.b);});
      break;
    case 9:
      if(!E(_ru/* seZX */.b)){
        return true;
      }else{
        return new F(function(){return _ri/* FormEngine.FormElement.Validation.validateElement2 */(_ru/* seZX */.c);});
      }
      break;
    case 10:
      return new F(function(){return _ri/* FormEngine.FormElement.Validation.validateElement2 */(_ru/* seZX */.b);});
      break;
    default:
      return true;
  }
},
_ry/* $wa */ = function(_rz/* s82C */, _rA/* s82D */, _rB/* s82E */, _/* EXTERNAL */){
  var _rC/* s82G */ = B(_ne/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_rz/* s82C */, _/* EXTERNAL */)),
  _rD/* s82K */ = B(_pM/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_rC/* s82G */, _rA/* s82D */, new T(function(){
    return B(_rs/* FormEngine.FormElement.Validation.validateElement */(_rC/* s82G */));
  },1), _/* EXTERNAL */)),
  _rE/* s82N */ = B(_qQ/* FormEngine.FormElement.Updating.applyRules1 */(_rz/* s82C */, _rA/* s82D */, _/* EXTERNAL */)),
  _rF/* s82U */ = E(E(_rB/* s82E */).b);
  if(!_rF/* s82U */._){
    return _0/* GHC.Tuple.() */;
  }else{
    return new F(function(){return A3(_rF/* s82U */.a,_rz/* s82C */, _rA/* s82D */, _/* EXTERNAL */);});
  }
},
_rG/* $wa1 */ = function(_rH/* s82W */, _rI/* s82X */, _rJ/* s82Y */, _/* EXTERNAL */){
  var _rK/* s830 */ = B(_ne/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_rH/* s82W */, _/* EXTERNAL */)),
  _rL/* s834 */ = B(_pM/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_rK/* s830 */, _rI/* s82X */, new T(function(){
    return B(_rs/* FormEngine.FormElement.Validation.validateElement */(_rK/* s830 */));
  },1), _/* EXTERNAL */)),
  _rM/* s837 */ = B(_qQ/* FormEngine.FormElement.Updating.applyRules1 */(_rH/* s82W */, _rI/* s82X */, _/* EXTERNAL */)),
  _rN/* s83e */ = E(E(_rJ/* s82Y */).a);
  if(!_rN/* s83e */._){
    return _0/* GHC.Tuple.() */;
  }else{
    return new F(function(){return A3(_rN/* s83e */.a,_rH/* s82W */, _rI/* s82X */, _/* EXTERNAL */);});
  }
},
_rO/* $wa1 */ = function(_rP/* slQP */, _rQ/* slQQ */, _/* EXTERNAL */){
  var _rR/* slQV */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _rQ/* slQQ */),
  _rS/* slR1 */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _rR/* slQV */),
  _rT/* slRc */ = eval/* EXTERNAL */(E(_o/* FormEngine.JQuery.addClass2 */)),
  _rU/* slRk */ = __app2/* EXTERNAL */(E(_rT/* slRc */), toJSStr/* EXTERNAL */(E(_rP/* slQP */)), _rS/* slR1 */);
  return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), _rU/* slRk */);});
},
_rV/* $wa23 */ = function(_rW/* slEm */, _rX/* slEn */, _/* EXTERNAL */){
  var _rY/* slEs */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _rX/* slEn */),
  _rZ/* slEy */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _rY/* slEs */),
  _s0/* slEC */ = B(_1r/* FormEngine.JQuery.onClick1 */(_rW/* slEm */, _rZ/* slEy */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_s0/* slEC */));});
},
_s1/* onMouseEnter2 */ = "(function (ev, jq) { jq.mouseenter(ev); })",
_s2/* onMouseEnter1 */ = function(_s3/* sltK */, _s4/* sltL */, _/* EXTERNAL */){
  var _s5/* sltX */ = __createJSFunc/* EXTERNAL */(2, function(_s6/* sltO */, _/* EXTERNAL */){
    var _s7/* sltQ */ = B(A2(E(_s3/* sltK */),_s6/* sltO */, _/* EXTERNAL */));
    return _1p/* Haste.Prim.Any.jsNull */;
  }),
  _s8/* slu0 */ = E(_s4/* sltL */),
  _s9/* slu5 */ = eval/* EXTERNAL */(E(_s1/* FormEngine.JQuery.onMouseEnter2 */)),
  _sa/* slud */ = __app2/* EXTERNAL */(E(_s9/* slu5 */), _s5/* sltX */, _s8/* slu0 */);
  return _s8/* slu0 */;
},
_sb/* $wa30 */ = function(_sc/* slET */, _sd/* slEU */, _/* EXTERNAL */){
  var _se/* slEZ */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _sd/* slEU */),
  _sf/* slF5 */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _se/* slEZ */),
  _sg/* slF9 */ = B(_s2/* FormEngine.JQuery.onMouseEnter1 */(_sc/* slET */, _sf/* slF5 */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_sg/* slF9 */));});
},
_sh/* onMouseLeave2 */ = "(function (ev, jq) { jq.mouseleave(ev); })",
_si/* onMouseLeave1 */ = function(_sj/* sltb */, _sk/* sltc */, _/* EXTERNAL */){
  var _sl/* slto */ = __createJSFunc/* EXTERNAL */(2, function(_sm/* sltf */, _/* EXTERNAL */){
    var _sn/* slth */ = B(A2(E(_sj/* sltb */),_sm/* sltf */, _/* EXTERNAL */));
    return _1p/* Haste.Prim.Any.jsNull */;
  }),
  _so/* sltr */ = E(_sk/* sltc */),
  _sp/* sltw */ = eval/* EXTERNAL */(E(_sh/* FormEngine.JQuery.onMouseLeave2 */)),
  _sq/* sltE */ = __app2/* EXTERNAL */(E(_sp/* sltw */), _sl/* slto */, _so/* sltr */);
  return _so/* sltr */;
},
_sr/* $wa31 */ = function(_ss/* slFq */, _st/* slFr */, _/* EXTERNAL */){
  var _su/* slFw */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _st/* slFr */),
  _sv/* slFC */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _su/* slFw */),
  _sw/* slFG */ = B(_si/* FormEngine.JQuery.onMouseLeave1 */(_ss/* slFq */, _sv/* slFC */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_sw/* slFG */));});
},
_sx/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<span class=\'short-desc\'>"));
}),
_sy/* setTextInside1 */ = function(_sz/* slWU */, _sA/* slWV */, _/* EXTERNAL */){
  return new F(function(){return _12/* FormEngine.JQuery.$wa34 */(_sz/* slWU */, E(_sA/* slWV */), _/* EXTERNAL */);});
},
_sB/* a1 */ = function(_sC/* s81J */, _sD/* s81K */, _/* EXTERNAL */){
  var _sE/* s81Z */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_sC/* s81J */)))).e);
  if(!_sE/* s81Z */._){
    return _sD/* s81K */;
  }else{
    var _sF/* s823 */ = B(_X/* FormEngine.JQuery.$wa3 */(_sx/* FormEngine.FormElement.Rendering.lvl */, E(_sD/* s81K */), _/* EXTERNAL */));
    return new F(function(){return _sy/* FormEngine.JQuery.setTextInside1 */(_sE/* s81Z */.a, _sF/* s823 */, _/* EXTERNAL */);});
  }
},
_sG/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<label>"));
}),
_sH/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<label class=\"link\" onclick=\""));
}),
_sI/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\">"));
}),
_sJ/* a2 */ = function(_sK/* s826 */, _sL/* s827 */, _/* EXTERNAL */){
  var _sM/* s82a */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_sK/* s826 */)))),
  _sN/* s82m */ = E(_sM/* s82a */.a);
  if(!_sN/* s82m */._){
    return _sL/* s827 */;
  }else{
    var _sO/* s82n */ = _sN/* s82m */.a,
    _sP/* s82o */ = E(_sM/* s82a */.i);
    if(!_sP/* s82o */._){
      var _sQ/* s82r */ = B(_X/* FormEngine.JQuery.$wa3 */(_sG/* FormEngine.FormElement.Rendering.lvl1 */, E(_sL/* s827 */), _/* EXTERNAL */));
      return new F(function(){return _sy/* FormEngine.JQuery.setTextInside1 */(_sO/* s82n */, _sQ/* s82r */, _/* EXTERNAL */);});
    }else{
      var _sR/* s82z */ = B(_X/* FormEngine.JQuery.$wa3 */(B(_7/* GHC.Base.++ */(_sH/* FormEngine.FormElement.Rendering.lvl2 */, new T(function(){
        return B(_7/* GHC.Base.++ */(_sP/* s82o */.a, _sI/* FormEngine.FormElement.Rendering.lvl3 */));
      },1))), E(_sL/* s827 */), _/* EXTERNAL */));
      return new F(function(){return _sy/* FormEngine.JQuery.setTextInside1 */(_sO/* s82n */, _sR/* s82z */, _/* EXTERNAL */);});
    }
  }
},
_sS/* a3 */ = function(_sT/* s83g */, _/* EXTERNAL */){
  var _sU/* s83k */ = B(_2E/* FormEngine.JQuery.select1 */(B(unAppCStr/* EXTERNAL */("#", new T(function(){
    return B(_4R/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId */(_sT/* s83g */));
  }))), _/* EXTERNAL */)),
  _sV/* s83p */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2X/* FormEngine.JQuery.disappearJq2 */, E(_sU/* s83k */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_sW/* setHtml2 */ = "(function (html, jq) { jq.html(html); return jq; })",
_sX/* $wa26 */ = function(_sY/* slUy */, _sZ/* slUz */, _/* EXTERNAL */){
  var _t0/* slUJ */ = eval/* EXTERNAL */(E(_sW/* FormEngine.JQuery.setHtml2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_t0/* slUJ */), toJSStr/* EXTERNAL */(E(_sY/* slUy */)), _sZ/* slUz */);});
},
_t1/* findSelector2 */ = "(function (elJs, jq) { return jq.find(elJs); })",
_t2/* $wa9 */ = function(_t3/* slX2 */, _t4/* slX3 */, _/* EXTERNAL */){
  var _t5/* slXd */ = eval/* EXTERNAL */(E(_t1/* FormEngine.JQuery.findSelector2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_t5/* slXd */), toJSStr/* EXTERNAL */(E(_t3/* slX2 */)), _t4/* slX3 */);});
},
_t6/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("span"));
}),
_t7/* a4 */ = function(_t8/* s83s */, _/* EXTERNAL */){
  var _t9/* s83w */ = B(_2E/* FormEngine.JQuery.select1 */(B(unAppCStr/* EXTERNAL */("#", new T(function(){
    return B(_4R/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId */(_t8/* s83s */));
  }))), _/* EXTERNAL */)),
  _ta/* s83z */ = E(_t9/* s83w */),
  _tb/* s83B */ = B(_t2/* FormEngine.JQuery.$wa9 */(_t6/* FormEngine.FormElement.Rendering.lvl4 */, _ta/* s83z */, _/* EXTERNAL */)),
  _tc/* s83R */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_t8/* s83s */)))).f);
  if(!_tc/* s83R */._){
    return _0/* GHC.Tuple.() */;
  }else{
    var _td/* s83V */ = B(_sX/* FormEngine.JQuery.$wa26 */(_tc/* s83R */.a, E(_tb/* s83B */), _/* EXTERNAL */)),
    _te/* s83Y */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2l/* FormEngine.JQuery.appearJq2 */, _ta/* s83z */, _/* EXTERNAL */));
    return _0/* GHC.Tuple.() */;
  }
},
_tf/* funcImg */ = function(_tg/* sezj */){
  return E(E(_tg/* sezj */).a);
},
_th/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td class=\'labeltd\'>"));
}),
_ti/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("id"));
}),
_tj/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<table>"));
}),
_tk/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<tbody>"));
}),
_tl/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<tr>"));
}),
_tm/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td>"));
}),
_tn/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("more-space"));
}),
_to/* $wa2 */ = function(_tp/* s841 */, _tq/* s842 */, _tr/* s843 */, _ts/* s844 */, _tt/* s845 */, _/* EXTERNAL */){
  var _tu/* s847 */ = B(_X/* FormEngine.JQuery.$wa3 */(_tj/* FormEngine.FormElement.Rendering.lvl5 */, _tt/* s845 */, _/* EXTERNAL */)),
  _tv/* s84f */ = B(_sb/* FormEngine.JQuery.$wa30 */(function(_tw/* s84c */, _/* EXTERNAL */){
    return new F(function(){return _t7/* FormEngine.FormElement.Rendering.a4 */(_tq/* s842 */, _/* EXTERNAL */);});
  }, E(_tu/* s847 */), _/* EXTERNAL */)),
  _tx/* s84n */ = B(_sr/* FormEngine.JQuery.$wa31 */(function(_ty/* s84k */, _/* EXTERNAL */){
    return new F(function(){return _sS/* FormEngine.FormElement.Rendering.a3 */(_tq/* s842 */, _/* EXTERNAL */);});
  }, E(_tv/* s84f */), _/* EXTERNAL */)),
  _tz/* s84s */ = E(_B/* FormEngine.JQuery.addClassInside_f3 */),
  _tA/* s84v */ = __app1/* EXTERNAL */(_tz/* s84s */, E(_tx/* s84n */)),
  _tB/* s84y */ = E(_A/* FormEngine.JQuery.addClassInside_f2 */),
  _tC/* s84B */ = __app1/* EXTERNAL */(_tB/* s84y */, _tA/* s84v */),
  _tD/* s84E */ = B(_X/* FormEngine.JQuery.$wa3 */(_tk/* FormEngine.FormElement.Rendering.lvl6 */, _tC/* s84B */, _/* EXTERNAL */)),
  _tE/* s84K */ = __app1/* EXTERNAL */(_tz/* s84s */, E(_tD/* s84E */)),
  _tF/* s84O */ = __app1/* EXTERNAL */(_tB/* s84y */, _tE/* s84K */),
  _tG/* s84R */ = B(_X/* FormEngine.JQuery.$wa3 */(_tl/* FormEngine.FormElement.Rendering.lvl7 */, _tF/* s84O */, _/* EXTERNAL */)),
  _tH/* s84X */ = __app1/* EXTERNAL */(_tz/* s84s */, E(_tG/* s84R */)),
  _tI/* s851 */ = __app1/* EXTERNAL */(_tB/* s84y */, _tH/* s84X */),
  _tJ/* s858 */ = function(_/* EXTERNAL */, _tK/* s85a */){
    var _tL/* s85b */ = B(_X/* FormEngine.JQuery.$wa3 */(_th/* FormEngine.FormElement.Rendering.lvl10 */, _tK/* s85a */, _/* EXTERNAL */)),
    _tM/* s85h */ = __app1/* EXTERNAL */(_tz/* s84s */, E(_tL/* s85b */)),
    _tN/* s85l */ = __app1/* EXTERNAL */(_tB/* s84y */, _tM/* s85h */),
    _tO/* s85o */ = B(_p/* FormEngine.JQuery.$wa */(_tn/* FormEngine.FormElement.Rendering.lvl9 */, _tN/* s85l */, _/* EXTERNAL */)),
    _tP/* s85r */ = B(_sJ/* FormEngine.FormElement.Rendering.a2 */(_tq/* s842 */, _tO/* s85o */, _/* EXTERNAL */)),
    _tQ/* s85w */ = E(_z/* FormEngine.JQuery.addClassInside_f1 */),
    _tR/* s85z */ = __app1/* EXTERNAL */(_tQ/* s85w */, E(_tP/* s85r */)),
    _tS/* s85C */ = B(A1(_tp/* s841 */,_/* EXTERNAL */)),
    _tT/* s85F */ = B(_X/* FormEngine.JQuery.$wa3 */(_tm/* FormEngine.FormElement.Rendering.lvl8 */, _tR/* s85z */, _/* EXTERNAL */)),
    _tU/* s85L */ = __app1/* EXTERNAL */(_tz/* s84s */, E(_tT/* s85F */)),
    _tV/* s85P */ = __app1/* EXTERNAL */(_tB/* s84y */, _tU/* s85L */),
    _tW/* s85X */ = __app2/* EXTERNAL */(E(_19/* FormEngine.JQuery.appendJq_f1 */), E(_tS/* s85C */), _tV/* s85P */),
    _tX/* s861 */ = __app1/* EXTERNAL */(_tQ/* s85w */, _tW/* s85X */),
    _tY/* s864 */ = B(_X/* FormEngine.JQuery.$wa3 */(_tm/* FormEngine.FormElement.Rendering.lvl8 */, _tX/* s861 */, _/* EXTERNAL */)),
    _tZ/* s86a */ = B(_C/* FormEngine.JQuery.$wa20 */(_ti/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
      return B(_pD/* FormEngine.FormElement.Identifiers.flagPlaceId */(_tq/* s842 */));
    },1), E(_tY/* s864 */), _/* EXTERNAL */)),
    _u0/* s86g */ = __app1/* EXTERNAL */(_tQ/* s85w */, E(_tZ/* s86a */)),
    _u1/* s86k */ = __app1/* EXTERNAL */(_tQ/* s85w */, _u0/* s86g */),
    _u2/* s86o */ = __app1/* EXTERNAL */(_tQ/* s85w */, _u1/* s86k */);
    return new F(function(){return _sB/* FormEngine.FormElement.Rendering.a1 */(_tq/* s842 */, _u2/* s86o */, _/* EXTERNAL */);});
  },
  _u3/* s86s */ = E(E(_ts/* s844 */).c);
  if(!_u3/* s86s */._){
    return new F(function(){return _tJ/* s858 */(_/* EXTERNAL */, _tI/* s851 */);});
  }else{
    var _u4/* s86t */ = _u3/* s86s */.a,
    _u5/* s86u */ = B(_X/* FormEngine.JQuery.$wa3 */(_tm/* FormEngine.FormElement.Rendering.lvl8 */, _tI/* s851 */, _/* EXTERNAL */)),
    _u6/* s86A */ = __app1/* EXTERNAL */(_tz/* s84s */, E(_u5/* s86u */)),
    _u7/* s86E */ = __app1/* EXTERNAL */(_tB/* s84y */, _u6/* s86A */),
    _u8/* s86H */ = B(_p/* FormEngine.JQuery.$wa */(_tn/* FormEngine.FormElement.Rendering.lvl9 */, _u7/* s86E */, _/* EXTERNAL */)),
    _u9/* s86N */ = B(_X/* FormEngine.JQuery.$wa3 */(B(_tf/* FormEngine.Functionality.funcImg */(_u4/* s86t */)), E(_u8/* s86H */), _/* EXTERNAL */)),
    _ua/* s86S */ = new T(function(){
      return B(A2(E(_u4/* s86t */).b,_tq/* s842 */, _tr/* s843 */));
    }),
    _ub/* s86Y */ = B(_rV/* FormEngine.JQuery.$wa23 */(function(_uc/* s86W */){
      return E(_ua/* s86S */);
    }, E(_u9/* s86N */), _/* EXTERNAL */)),
    _ud/* s876 */ = __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_ub/* s86Y */));
    return new F(function(){return _tJ/* s858 */(_/* EXTERNAL */, _ud/* s876 */);});
  }
},
_ue/* a5 */ = function(_uf/* s87e */, _/* EXTERNAL */){
  while(1){
    var _ug/* s87g */ = E(_uf/* s87e */);
    if(!_ug/* s87g */._){
      return _0/* GHC.Tuple.() */;
    }else{
      var _uh/* s87l */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2X/* FormEngine.JQuery.disappearJq2 */, E(_ug/* s87g */.a), _/* EXTERNAL */));
      _uf/* s87e */ = _ug/* s87g */.b;
      continue;
    }
  }
},
_ui/* appendT1 */ = function(_uj/* slPK */, _uk/* slPL */, _/* EXTERNAL */){
  return new F(function(){return _X/* FormEngine.JQuery.$wa3 */(_uj/* slPK */, E(_uk/* slPL */), _/* EXTERNAL */);});
},
_ul/* checkboxId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_optional_group"));
}),
_um/* checkboxId */ = function(_un/* sfN2 */){
  return new F(function(){return _7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_un/* sfN2 */)))).b)), _ul/* FormEngine.FormElement.Identifiers.checkboxId1 */);});
},
_uo/* errorjq1 */ = function(_up/* slz3 */, _uq/* slz4 */, _/* EXTERNAL */){
  var _ur/* slze */ = eval/* EXTERNAL */(E(_2/* FormEngine.JQuery.errorIO2 */)),
  _us/* slzm */ = __app1/* EXTERNAL */(E(_ur/* slze */), toJSStr/* EXTERNAL */(E(_up/* slz3 */)));
  return _uq/* slz4 */;
},
_ut/* go */ = function(_uu/* s879 */, _uv/* s87a */){
  while(1){
    var _uw/* s87b */ = E(_uu/* s879 */);
    if(!_uw/* s87b */._){
      return E(_uv/* s87a */);
    }else{
      _uu/* s879 */ = _uw/* s87b */.b;
      _uv/* s87a */ = _uw/* s87b */.a;
      continue;
    }
  }
},
_ux/* ifiText1 */ = new T(function(){
  return B(_oF/* Control.Exception.Base.recSelError */("ifiText"));
}),
_uy/* isChecked_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.prop(\'checked\') === true; })");
}),
_uz/* isRadioSelected_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.length; })");
}),
_uA/* isRadioSelected1 */ = function(_uB/* slLP */, _/* EXTERNAL */){
  var _uC/* slM0 */ = eval/* EXTERNAL */(E(_89/* FormEngine.JQuery.getRadioValue2 */)),
  _uD/* slM8 */ = __app1/* EXTERNAL */(E(_uC/* slM0 */), toJSStr/* EXTERNAL */(B(_7/* GHC.Base.++ */(_8b/* FormEngine.JQuery.getRadioValue4 */, new T(function(){
    return B(_7/* GHC.Base.++ */(_uB/* slLP */, _8a/* FormEngine.JQuery.getRadioValue3 */));
  },1))))),
  _uE/* slMe */ = __app1/* EXTERNAL */(E(_uz/* FormEngine.JQuery.isRadioSelected_f1 */), _uD/* slM8 */);
  return new T(function(){
    var _uF/* slMi */ = Number/* EXTERNAL */(_uE/* slMe */),
    _uG/* slMm */ = jsTrunc/* EXTERNAL */(_uF/* slMi */);
    return _uG/* slMm */>0;
  });
},
_uH/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": empty list"));
}),
_uI/* errorEmptyList */ = function(_uJ/* s9sr */){
  return new F(function(){return err/* EXTERNAL */(B(_7/* GHC.Base.++ */(_5F/* GHC.List.prel_list_str */, new T(function(){
    return B(_7/* GHC.Base.++ */(_uJ/* s9sr */, _uH/* GHC.List.lvl */));
  },1))));});
},
_uK/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("last"));
}),
_uL/* last1 */ = new T(function(){
  return B(_uI/* GHC.List.errorEmptyList */(_uK/* GHC.List.lvl16 */));
}),
_uM/* lfiAvailableOptions1 */ = new T(function(){
  return B(_oF/* Control.Exception.Base.recSelError */("lfiAvailableOptions"));
}),
_uN/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Submit"));
}),
_uO/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("value"));
}),
_uP/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'button\' class=\'submit\'>"));
}),
_uQ/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td class=\'labeltd more-space\' style=\'text-align: center\'>"));
}),
_uR/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<table style=\'margin-top: 10px\'>"));
}),
_uS/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Save"));
}),
_uT/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'submit\'>"));
}),
_uU/* lvl19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MultipleGroupElement rendering not implemented yet"));
}),
_uV/* lvl20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'optional-section\'>"));
}),
_uW/* lvl21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\u25be"));
}),
_uX/* lvl22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_uY/* lvl23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("checked"));
}),
_uZ/* lvl24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("name"));
}),
_v0/* lvl25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'checkbox\'>"));
}),
_v1/* lvl26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("level"));
}),
_v2/* lvl27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'optional-group\'>"));
}),
_v3/* lvl28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(">"));
}),
_v4/* lvl29 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<h"));
}),
_v5/* lvl30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("framed"));
}),
_v6/* lvl31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'simple-group\'>"));
}),
_v7/* lvl32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("selected"));
}),
_v8/* lvl33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<option>"));
}),
_v9/* lvl34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("identity"));
}),
_va/* lvl35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<select>"));
}),
_vb/* lvl36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div>"));
}),
_vc/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<br>"));
}),
_vd/* lvl38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'radio\'>"));
}),
_ve/* lvl39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div></div>"));
}),
_vf/* lvl40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td class=\'more-space info\' colspan=\'2\'>"));
}),
_vg/* lvl41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("&nbsp;&nbsp;"));
}),
_vh/* lvl42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("&nbsp;"));
}),
_vi/* lvl43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'number\'>"));
}),
_vj/* lvl44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'email\'>"));
}),
_vk/* lvl45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<textarea>"));
}),
_vl/* lvl46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'text\'>"));
}),
_vm/* lvl47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("renderElement did not unify"));
}),
_vn/* lvl48 */ = new T(function(){
  return B(_1M/* GHC.Show.$wshowSignedInt */(0, 0, _k/* GHC.Types.[] */));
}),
_vo/* onBlur2 */ = "(function (ev, jq) { jq.blur(ev); })",
_vp/* onBlur1 */ = function(_vq/* slw0 */, _vr/* slw1 */, _/* EXTERNAL */){
  var _vs/* slwd */ = __createJSFunc/* EXTERNAL */(2, function(_vt/* slw4 */, _/* EXTERNAL */){
    var _vu/* slw6 */ = B(A2(E(_vq/* slw0 */),_vt/* slw4 */, _/* EXTERNAL */));
    return _1p/* Haste.Prim.Any.jsNull */;
  }),
  _vv/* slwg */ = E(_vr/* slw1 */),
  _vw/* slwl */ = eval/* EXTERNAL */(E(_vo/* FormEngine.JQuery.onBlur2 */)),
  _vx/* slwt */ = __app2/* EXTERNAL */(E(_vw/* slwl */), _vs/* slwd */, _vv/* slwg */);
  return _vv/* slwg */;
},
_vy/* onChange2 */ = "(function (ev, jq) { jq.change(ev); })",
_vz/* onChange1 */ = function(_vA/* sluj */, _vB/* sluk */, _/* EXTERNAL */){
  var _vC/* sluw */ = __createJSFunc/* EXTERNAL */(2, function(_vD/* slun */, _/* EXTERNAL */){
    var _vE/* slup */ = B(A2(E(_vA/* sluj */),_vD/* slun */, _/* EXTERNAL */));
    return _1p/* Haste.Prim.Any.jsNull */;
  }),
  _vF/* sluz */ = E(_vB/* sluk */),
  _vG/* sluE */ = eval/* EXTERNAL */(E(_vy/* FormEngine.JQuery.onChange2 */)),
  _vH/* sluM */ = __app2/* EXTERNAL */(E(_vG/* sluE */), _vC/* sluw */, _vF/* sluz */);
  return _vF/* sluz */;
},
_vI/* onKeyup2 */ = "(function (ev, jq) { jq.keyup(ev); })",
_vJ/* onKeyup1 */ = function(_vK/* slvr */, _vL/* slvs */, _/* EXTERNAL */){
  var _vM/* slvE */ = __createJSFunc/* EXTERNAL */(2, function(_vN/* slvv */, _/* EXTERNAL */){
    var _vO/* slvx */ = B(A2(E(_vK/* slvr */),_vN/* slvv */, _/* EXTERNAL */));
    return _1p/* Haste.Prim.Any.jsNull */;
  }),
  _vP/* slvH */ = E(_vL/* slvs */),
  _vQ/* slvM */ = eval/* EXTERNAL */(E(_vI/* FormEngine.JQuery.onKeyup2 */)),
  _vR/* slvU */ = __app2/* EXTERNAL */(E(_vQ/* slvM */), _vM/* slvE */, _vP/* slvH */);
  return _vP/* slvH */;
},
_vS/* optionElemValue */ = function(_vT/* scb6 */){
  var _vU/* scb7 */ = E(_vT/* scb6 */);
  if(!_vU/* scb7 */._){
    var _vV/* scba */ = E(_vU/* scb7 */.a);
    return (_vV/* scba */._==0) ? E(_vV/* scba */.a) : E(_vV/* scba */.b);
  }else{
    var _vW/* scbi */ = E(_vU/* scb7 */.a);
    return (_vW/* scbi */._==0) ? E(_vW/* scbi */.a) : E(_vW/* scbi */.b);
  }
},
_vX/* optionSectionId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_detail"));
}),
_vY/* filter */ = function(_vZ/*  s9DD */, _w0/*  s9DE */){
  while(1){
    var _w1/*  filter */ = B((function(_w2/* s9DD */, _w3/* s9DE */){
      var _w4/* s9DF */ = E(_w3/* s9DE */);
      if(!_w4/* s9DF */._){
        return __Z/* EXTERNAL */;
      }else{
        var _w5/* s9DG */ = _w4/* s9DF */.a,
        _w6/* s9DH */ = _w4/* s9DF */.b;
        if(!B(A1(_w2/* s9DD */,_w5/* s9DG */))){
          var _w7/*   s9DD */ = _w2/* s9DD */;
          _vZ/*  s9DD */ = _w7/*   s9DD */;
          _w0/*  s9DE */ = _w6/* s9DH */;
          return __continue/* EXTERNAL */;
        }else{
          return new T2(1,_w5/* s9DG */,new T(function(){
            return B(_vY/* GHC.List.filter */(_w2/* s9DD */, _w6/* s9DH */));
          }));
        }
      }
    })(_vZ/*  s9DD */, _w0/*  s9DE */));
    if(_w1/*  filter */!=__continue/* EXTERNAL */){
      return _w1/*  filter */;
    }
  }
},
_w8/* $wlvl */ = function(_w9/* sfNh */){
  var _wa/* sfNi */ = function(_wb/* sfNj */){
    var _wc/* sfNk */ = function(_wd/* sfNl */){
      if(_w9/* sfNh */<48){
        switch(E(_w9/* sfNh */)){
          case 45:
            return true;
          case 95:
            return true;
          default:
            return false;
        }
      }else{
        if(_w9/* sfNh */>57){
          switch(E(_w9/* sfNh */)){
            case 45:
              return true;
            case 95:
              return true;
            default:
              return false;
          }
        }else{
          return true;
        }
      }
    };
    if(_w9/* sfNh */<97){
      return new F(function(){return _wc/* sfNk */(_/* EXTERNAL */);});
    }else{
      if(_w9/* sfNh */>122){
        return new F(function(){return _wc/* sfNk */(_/* EXTERNAL */);});
      }else{
        return true;
      }
    }
  };
  if(_w9/* sfNh */<65){
    return new F(function(){return _wa/* sfNi */(_/* EXTERNAL */);});
  }else{
    if(_w9/* sfNh */>90){
      return new F(function(){return _wa/* sfNi */(_/* EXTERNAL */);});
    }else{
      return true;
    }
  }
},
_we/* radioId1 */ = function(_wf/* sfNA */){
  return new F(function(){return _w8/* FormEngine.FormElement.Identifiers.$wlvl */(E(_wf/* sfNA */));});
},
_wg/* radioId2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_"));
}),
_wh/* radioId */ = function(_wi/* sfND */, _wj/* sfNE */){
  var _wk/* sfOa */ = new T(function(){
    return B(_7/* GHC.Base.++ */(_wg/* FormEngine.FormElement.Identifiers.radioId2 */, new T(function(){
      var _wl/* sfNT */ = E(_wj/* sfNE */);
      if(!_wl/* sfNT */._){
        var _wm/* sfNW */ = E(_wl/* sfNT */.a);
        if(!_wm/* sfNW */._){
          return B(_vY/* GHC.List.filter */(_we/* FormEngine.FormElement.Identifiers.radioId1 */, _wm/* sfNW */.a));
        }else{
          return B(_vY/* GHC.List.filter */(_we/* FormEngine.FormElement.Identifiers.radioId1 */, _wm/* sfNW */.b));
        }
      }else{
        var _wn/* sfO4 */ = E(_wl/* sfNT */.a);
        if(!_wn/* sfO4 */._){
          return B(_vY/* GHC.List.filter */(_we/* FormEngine.FormElement.Identifiers.radioId1 */, _wn/* sfO4 */.a));
        }else{
          return B(_vY/* GHC.List.filter */(_we/* FormEngine.FormElement.Identifiers.radioId1 */, _wn/* sfO4 */.b));
        }
      }
    },1)));
  },1);
  return new F(function(){return _7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_wi/* sfND */)))).b)), _wk/* sfOa */);});
},
_wo/* target_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (js) {return $(js.target); })");
}),
_wp/* foldElements2 */ = function(_wq/* s87o */, _wr/* s87p */, _ws/* s87q */, _wt/* s87r */, _/* EXTERNAL */){
  var _wu/* s87t */ = function(_wv/* s87u */, _/* EXTERNAL */){
    return new F(function(){return _rG/* FormEngine.FormElement.Rendering.$wa1 */(_wq/* s87o */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
  },
  _ww/* s87w */ = E(_wq/* s87o */);
  switch(_ww/* s87w */._){
    case 0:
      return new F(function(){return _uo/* FormEngine.JQuery.errorjq1 */(_vm/* FormEngine.FormElement.Rendering.lvl47 */, _wt/* s87r */, _/* EXTERNAL */);});
      break;
    case 1:
      var _wx/* s88I */ = function(_/* EXTERNAL */){
        var _wy/* s87G */ = B(_2E/* FormEngine.JQuery.select1 */(_vl/* FormEngine.FormElement.Rendering.lvl46 */, _/* EXTERNAL */)),
        _wz/* s87J */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(_ww/* s87w */.a)),
        _wA/* s87Y */ = B(_u/* FormEngine.JQuery.$wa6 */(_uZ/* FormEngine.FormElement.Rendering.lvl24 */, B(_27/* FormEngine.FormItem.numbering2text */(_wz/* s87J */.b)), E(_wy/* s87G */), _/* EXTERNAL */)),
        _wB/* s881 */ = function(_/* EXTERNAL */, _wC/* s883 */){
          var _wD/* s884 */ = B(_u/* FormEngine.JQuery.$wa6 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, _ww/* s87w */.b, _wC/* s883 */, _/* EXTERNAL */)),
          _wE/* s88a */ = B(_s2/* FormEngine.JQuery.onMouseEnter1 */(function(_wF/* s887 */, _/* EXTERNAL */){
            return new F(function(){return _rG/* FormEngine.FormElement.Rendering.$wa1 */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
          }, _wD/* s884 */, _/* EXTERNAL */)),
          _wG/* s88g */ = B(_vJ/* FormEngine.JQuery.onKeyup1 */(function(_wH/* s88d */, _/* EXTERNAL */){
            return new F(function(){return _rG/* FormEngine.FormElement.Rendering.$wa1 */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
          }, _wE/* s88a */, _/* EXTERNAL */)),
          _wI/* s88m */ = B(_vp/* FormEngine.JQuery.onBlur1 */(function(_wJ/* s88j */, _/* EXTERNAL */){
            return new F(function(){return _ry/* FormEngine.FormElement.Rendering.$wa */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
          }, _wG/* s88g */, _/* EXTERNAL */));
          return new F(function(){return _si/* FormEngine.JQuery.onMouseLeave1 */(function(_wK/* s88p */, _/* EXTERNAL */){
            return new F(function(){return _ry/* FormEngine.FormElement.Rendering.$wa */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
          }, _wI/* s88m */, _/* EXTERNAL */);});
        },
        _wL/* s88s */ = E(_wz/* s87J */.c);
        if(!_wL/* s88s */._){
          var _wM/* s88v */ = B(_u/* FormEngine.JQuery.$wa6 */(_v9/* FormEngine.FormElement.Rendering.lvl34 */, _k/* GHC.Types.[] */, E(_wA/* s87Y */), _/* EXTERNAL */));
          return new F(function(){return _wB/* s881 */(_/* EXTERNAL */, E(_wM/* s88v */));});
        }else{
          var _wN/* s88D */ = B(_u/* FormEngine.JQuery.$wa6 */(_v9/* FormEngine.FormElement.Rendering.lvl34 */, _wL/* s88s */.a, E(_wA/* s87Y */), _/* EXTERNAL */));
          return new F(function(){return _wB/* s881 */(_/* EXTERNAL */, E(_wN/* s88D */));});
        }
      };
      return new F(function(){return _to/* FormEngine.FormElement.Rendering.$wa2 */(_wx/* s88I */, _ww/* s87w */, _wr/* s87p */, _ws/* s87q */, E(_wt/* s87r */), _/* EXTERNAL */);});
      break;
    case 2:
      var _wO/* s89R */ = function(_/* EXTERNAL */){
        var _wP/* s88P */ = B(_2E/* FormEngine.JQuery.select1 */(_vk/* FormEngine.FormElement.Rendering.lvl45 */, _/* EXTERNAL */)),
        _wQ/* s88S */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(_ww/* s87w */.a)),
        _wR/* s897 */ = B(_u/* FormEngine.JQuery.$wa6 */(_uZ/* FormEngine.FormElement.Rendering.lvl24 */, B(_27/* FormEngine.FormItem.numbering2text */(_wQ/* s88S */.b)), E(_wP/* s88P */), _/* EXTERNAL */)),
        _wS/* s89a */ = function(_/* EXTERNAL */, _wT/* s89c */){
          var _wU/* s89d */ = B(_u/* FormEngine.JQuery.$wa6 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, _ww/* s87w */.b, _wT/* s89c */, _/* EXTERNAL */)),
          _wV/* s89j */ = B(_s2/* FormEngine.JQuery.onMouseEnter1 */(function(_wW/* s89g */, _/* EXTERNAL */){
            return new F(function(){return _rG/* FormEngine.FormElement.Rendering.$wa1 */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
          }, _wU/* s89d */, _/* EXTERNAL */)),
          _wX/* s89p */ = B(_vJ/* FormEngine.JQuery.onKeyup1 */(function(_wY/* s89m */, _/* EXTERNAL */){
            return new F(function(){return _rG/* FormEngine.FormElement.Rendering.$wa1 */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
          }, _wV/* s89j */, _/* EXTERNAL */)),
          _wZ/* s89v */ = B(_vp/* FormEngine.JQuery.onBlur1 */(function(_x0/* s89s */, _/* EXTERNAL */){
            return new F(function(){return _ry/* FormEngine.FormElement.Rendering.$wa */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
          }, _wX/* s89p */, _/* EXTERNAL */));
          return new F(function(){return _si/* FormEngine.JQuery.onMouseLeave1 */(function(_x1/* s89y */, _/* EXTERNAL */){
            return new F(function(){return _ry/* FormEngine.FormElement.Rendering.$wa */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
          }, _wZ/* s89v */, _/* EXTERNAL */);});
        },
        _x2/* s89B */ = E(_wQ/* s88S */.c);
        if(!_x2/* s89B */._){
          var _x3/* s89E */ = B(_u/* FormEngine.JQuery.$wa6 */(_v9/* FormEngine.FormElement.Rendering.lvl34 */, _k/* GHC.Types.[] */, E(_wR/* s897 */), _/* EXTERNAL */));
          return new F(function(){return _wS/* s89a */(_/* EXTERNAL */, E(_x3/* s89E */));});
        }else{
          var _x4/* s89M */ = B(_u/* FormEngine.JQuery.$wa6 */(_v9/* FormEngine.FormElement.Rendering.lvl34 */, _x2/* s89B */.a, E(_wR/* s897 */), _/* EXTERNAL */));
          return new F(function(){return _wS/* s89a */(_/* EXTERNAL */, E(_x4/* s89M */));});
        }
      };
      return new F(function(){return _to/* FormEngine.FormElement.Rendering.$wa2 */(_wO/* s89R */, _ww/* s87w */, _wr/* s87p */, _ws/* s87q */, E(_wt/* s87r */), _/* EXTERNAL */);});
      break;
    case 3:
      var _x5/* s8b0 */ = function(_/* EXTERNAL */){
        var _x6/* s89Y */ = B(_2E/* FormEngine.JQuery.select1 */(_vj/* FormEngine.FormElement.Rendering.lvl44 */, _/* EXTERNAL */)),
        _x7/* s8a1 */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(_ww/* s87w */.a)),
        _x8/* s8ag */ = B(_u/* FormEngine.JQuery.$wa6 */(_uZ/* FormEngine.FormElement.Rendering.lvl24 */, B(_27/* FormEngine.FormItem.numbering2text */(_x7/* s8a1 */.b)), E(_x6/* s89Y */), _/* EXTERNAL */)),
        _x9/* s8aj */ = function(_/* EXTERNAL */, _xa/* s8al */){
          var _xb/* s8am */ = B(_u/* FormEngine.JQuery.$wa6 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, _ww/* s87w */.b, _xa/* s8al */, _/* EXTERNAL */)),
          _xc/* s8as */ = B(_s2/* FormEngine.JQuery.onMouseEnter1 */(function(_xd/* s8ap */, _/* EXTERNAL */){
            return new F(function(){return _rG/* FormEngine.FormElement.Rendering.$wa1 */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
          }, _xb/* s8am */, _/* EXTERNAL */)),
          _xe/* s8ay */ = B(_vJ/* FormEngine.JQuery.onKeyup1 */(function(_xf/* s8av */, _/* EXTERNAL */){
            return new F(function(){return _rG/* FormEngine.FormElement.Rendering.$wa1 */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
          }, _xc/* s8as */, _/* EXTERNAL */)),
          _xg/* s8aE */ = B(_vp/* FormEngine.JQuery.onBlur1 */(function(_xh/* s8aB */, _/* EXTERNAL */){
            return new F(function(){return _ry/* FormEngine.FormElement.Rendering.$wa */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
          }, _xe/* s8ay */, _/* EXTERNAL */));
          return new F(function(){return _si/* FormEngine.JQuery.onMouseLeave1 */(function(_xi/* s8aH */, _/* EXTERNAL */){
            return new F(function(){return _ry/* FormEngine.FormElement.Rendering.$wa */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
          }, _xg/* s8aE */, _/* EXTERNAL */);});
        },
        _xj/* s8aK */ = E(_x7/* s8a1 */.c);
        if(!_xj/* s8aK */._){
          var _xk/* s8aN */ = B(_u/* FormEngine.JQuery.$wa6 */(_v9/* FormEngine.FormElement.Rendering.lvl34 */, _k/* GHC.Types.[] */, E(_x8/* s8ag */), _/* EXTERNAL */));
          return new F(function(){return _x9/* s8aj */(_/* EXTERNAL */, E(_xk/* s8aN */));});
        }else{
          var _xl/* s8aV */ = B(_u/* FormEngine.JQuery.$wa6 */(_v9/* FormEngine.FormElement.Rendering.lvl34 */, _xj/* s8aK */.a, E(_x8/* s8ag */), _/* EXTERNAL */));
          return new F(function(){return _x9/* s8aj */(_/* EXTERNAL */, E(_xl/* s8aV */));});
        }
      };
      return new F(function(){return _to/* FormEngine.FormElement.Rendering.$wa2 */(_x5/* s8b0 */, _ww/* s87w */, _wr/* s87p */, _ws/* s87q */, E(_wt/* s87r */), _/* EXTERNAL */);});
      break;
    case 4:
      var _xm/* s8b1 */ = _ww/* s87w */.a,
      _xn/* s8b7 */ = function(_xo/* s8b8 */, _/* EXTERNAL */){
        return new F(function(){return _ry/* FormEngine.FormElement.Rendering.$wa */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
      },
      _xp/* s8gU */ = function(_/* EXTERNAL */){
        var _xq/* s8bb */ = B(_2E/* FormEngine.JQuery.select1 */(_vi/* FormEngine.FormElement.Rendering.lvl43 */, _/* EXTERNAL */)),
        _xr/* s8be */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(_xm/* s8b1 */)),
        _xs/* s8bg */ = _xr/* s8be */.b,
        _xt/* s8bt */ = B(_u/* FormEngine.JQuery.$wa6 */(_ti/* FormEngine.FormElement.Rendering.lvl11 */, B(_27/* FormEngine.FormItem.numbering2text */(_xs/* s8bg */)), E(_xq/* s8bb */), _/* EXTERNAL */)),
        _xu/* s8bz */ = B(_u/* FormEngine.JQuery.$wa6 */(_uZ/* FormEngine.FormElement.Rendering.lvl24 */, B(_27/* FormEngine.FormItem.numbering2text */(_xs/* s8bg */)), E(_xt/* s8bt */), _/* EXTERNAL */)),
        _xv/* s8bC */ = function(_/* EXTERNAL */, _xw/* s8bE */){
          var _xx/* s8bF */ = function(_/* EXTERNAL */, _xy/* s8bH */){
            var _xz/* s8bL */ = B(_s2/* FormEngine.JQuery.onMouseEnter1 */(function(_xA/* s8bI */, _/* EXTERNAL */){
              return new F(function(){return _rG/* FormEngine.FormElement.Rendering.$wa1 */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
            }, _xy/* s8bH */, _/* EXTERNAL */)),
            _xB/* s8bR */ = B(_vJ/* FormEngine.JQuery.onKeyup1 */(function(_xC/* s8bO */, _/* EXTERNAL */){
              return new F(function(){return _rG/* FormEngine.FormElement.Rendering.$wa1 */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
            }, _xz/* s8bL */, _/* EXTERNAL */)),
            _xD/* s8bX */ = B(_vp/* FormEngine.JQuery.onBlur1 */(function(_xE/* s8bU */, _/* EXTERNAL */){
              return new F(function(){return _ry/* FormEngine.FormElement.Rendering.$wa */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
            }, _xB/* s8bR */, _/* EXTERNAL */)),
            _xF/* s8c3 */ = B(_si/* FormEngine.JQuery.onMouseLeave1 */(function(_xG/* s8c0 */, _/* EXTERNAL */){
              return new F(function(){return _ry/* FormEngine.FormElement.Rendering.$wa */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
            }, _xD/* s8bX */, _/* EXTERNAL */)),
            _xH/* s8c8 */ = B(_X/* FormEngine.JQuery.$wa3 */(_vh/* FormEngine.FormElement.Rendering.lvl42 */, E(_xF/* s8c3 */), _/* EXTERNAL */)),
            _xI/* s8cb */ = E(_xm/* s8b1 */);
            if(_xI/* s8cb */._==3){
              var _xJ/* s8cf */ = E(_xI/* s8cb */.b);
              switch(_xJ/* s8cf */._){
                case 0:
                  return new F(function(){return _ui/* FormEngine.JQuery.appendT1 */(_xJ/* s8cf */.a, _xH/* s8c8 */, _/* EXTERNAL */);});
                  break;
                case 1:
                  var _xK/* s8ci */ = new T(function(){
                    return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(E(_xI/* s8cb */.a).b)), _8k/* FormEngine.FormItem.nfiUnitId1 */));
                  }),
                  _xL/* s8cw */ = E(_xJ/* s8cf */.a);
                  if(!_xL/* s8cw */._){
                    return _xH/* s8c8 */;
                  }else{
                    var _xM/* s8cx */ = _xL/* s8cw */.a,
                    _xN/* s8cy */ = _xL/* s8cw */.b,
                    _xO/* s8cB */ = B(_X/* FormEngine.JQuery.$wa3 */(_vd/* FormEngine.FormElement.Rendering.lvl38 */, E(_xH/* s8c8 */), _/* EXTERNAL */)),
                    _xP/* s8cG */ = B(_C/* FormEngine.JQuery.$wa20 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, _xM/* s8cx */, E(_xO/* s8cB */), _/* EXTERNAL */)),
                    _xQ/* s8cL */ = B(_C/* FormEngine.JQuery.$wa20 */(_uZ/* FormEngine.FormElement.Rendering.lvl24 */, _xK/* s8ci */, E(_xP/* s8cG */), _/* EXTERNAL */)),
                    _xR/* s8cQ */ = B(_sb/* FormEngine.JQuery.$wa30 */(_wu/* s87t */, E(_xQ/* s8cL */), _/* EXTERNAL */)),
                    _xS/* s8cV */ = B(_rV/* FormEngine.JQuery.$wa23 */(_wu/* s87t */, E(_xR/* s8cQ */), _/* EXTERNAL */)),
                    _xT/* s8d0 */ = B(_sr/* FormEngine.JQuery.$wa31 */(_xn/* s8b7 */, E(_xS/* s8cV */), _/* EXTERNAL */)),
                    _xU/* s8d3 */ = function(_/* EXTERNAL */, _xV/* s8d5 */){
                      var _xW/* s8d6 */ = B(_X/* FormEngine.JQuery.$wa3 */(_sG/* FormEngine.FormElement.Rendering.lvl1 */, _xV/* s8d5 */, _/* EXTERNAL */)),
                      _xX/* s8db */ = B(_12/* FormEngine.JQuery.$wa34 */(_xM/* s8cx */, E(_xW/* s8d6 */), _/* EXTERNAL */));
                      return new F(function(){return _ui/* FormEngine.JQuery.appendT1 */(_vg/* FormEngine.FormElement.Rendering.lvl41 */, _xX/* s8db */, _/* EXTERNAL */);});
                    },
                    _xY/* s8de */ = E(_ww/* s87w */.c);
                    if(!_xY/* s8de */._){
                      var _xZ/* s8dh */ = B(_xU/* s8d3 */(_/* EXTERNAL */, E(_xT/* s8d0 */))),
                      _y0/* s8dk */ = function(_y1/* s8dl */, _y2/* s8dm */, _/* EXTERNAL */){
                        while(1){
                          var _y3/* s8do */ = E(_y1/* s8dl */);
                          if(!_y3/* s8do */._){
                            return _y2/* s8dm */;
                          }else{
                            var _y4/* s8dp */ = _y3/* s8do */.a,
                            _y5/* s8dt */ = B(_X/* FormEngine.JQuery.$wa3 */(_vd/* FormEngine.FormElement.Rendering.lvl38 */, E(_y2/* s8dm */), _/* EXTERNAL */)),
                            _y6/* s8dy */ = B(_C/* FormEngine.JQuery.$wa20 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, _y4/* s8dp */, E(_y5/* s8dt */), _/* EXTERNAL */)),
                            _y7/* s8dD */ = B(_C/* FormEngine.JQuery.$wa20 */(_uZ/* FormEngine.FormElement.Rendering.lvl24 */, _xK/* s8ci */, E(_y6/* s8dy */), _/* EXTERNAL */)),
                            _y8/* s8dI */ = B(_sb/* FormEngine.JQuery.$wa30 */(_wu/* s87t */, E(_y7/* s8dD */), _/* EXTERNAL */)),
                            _y9/* s8dN */ = B(_rV/* FormEngine.JQuery.$wa23 */(_wu/* s87t */, E(_y8/* s8dI */), _/* EXTERNAL */)),
                            _ya/* s8dS */ = B(_sr/* FormEngine.JQuery.$wa31 */(_xn/* s8b7 */, E(_y9/* s8dN */), _/* EXTERNAL */)),
                            _yb/* s8dX */ = B(_X/* FormEngine.JQuery.$wa3 */(_sG/* FormEngine.FormElement.Rendering.lvl1 */, E(_ya/* s8dS */), _/* EXTERNAL */)),
                            _yc/* s8e2 */ = B(_12/* FormEngine.JQuery.$wa34 */(_y4/* s8dp */, E(_yb/* s8dX */), _/* EXTERNAL */)),
                            _yd/* s8e7 */ = B(_X/* FormEngine.JQuery.$wa3 */(_vg/* FormEngine.FormElement.Rendering.lvl41 */, E(_yc/* s8e2 */), _/* EXTERNAL */));
                            _y1/* s8dl */ = _y3/* s8do */.b;
                            _y2/* s8dm */ = _yd/* s8e7 */;
                            continue;
                          }
                        }
                      };
                      return new F(function(){return _y0/* s8dk */(_xN/* s8cy */, _xZ/* s8dh */, _/* EXTERNAL */);});
                    }else{
                      var _ye/* s8ea */ = _xY/* s8de */.a;
                      if(!B(_2n/* GHC.Base.eqString */(_ye/* s8ea */, _xM/* s8cx */))){
                        var _yf/* s8ee */ = B(_xU/* s8d3 */(_/* EXTERNAL */, E(_xT/* s8d0 */))),
                        _yg/* s8eh */ = function(_yh/*  s8ei */, _yi/*  s8ej */, _/* EXTERNAL */){
                          while(1){
                            var _yj/*  s8eh */ = B((function(_yk/* s8ei */, _yl/* s8ej */, _/* EXTERNAL */){
                              var _ym/* s8el */ = E(_yk/* s8ei */);
                              if(!_ym/* s8el */._){
                                return _yl/* s8ej */;
                              }else{
                                var _yn/* s8em */ = _ym/* s8el */.a,
                                _yo/* s8en */ = _ym/* s8el */.b,
                                _yp/* s8eq */ = B(_X/* FormEngine.JQuery.$wa3 */(_vd/* FormEngine.FormElement.Rendering.lvl38 */, E(_yl/* s8ej */), _/* EXTERNAL */)),
                                _yq/* s8ev */ = B(_C/* FormEngine.JQuery.$wa20 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, _yn/* s8em */, E(_yp/* s8eq */), _/* EXTERNAL */)),
                                _yr/* s8eA */ = B(_C/* FormEngine.JQuery.$wa20 */(_uZ/* FormEngine.FormElement.Rendering.lvl24 */, _xK/* s8ci */, E(_yq/* s8ev */), _/* EXTERNAL */)),
                                _ys/* s8eF */ = B(_sb/* FormEngine.JQuery.$wa30 */(_wu/* s87t */, E(_yr/* s8eA */), _/* EXTERNAL */)),
                                _yt/* s8eK */ = B(_rV/* FormEngine.JQuery.$wa23 */(_wu/* s87t */, E(_ys/* s8eF */), _/* EXTERNAL */)),
                                _yu/* s8eP */ = B(_sr/* FormEngine.JQuery.$wa31 */(_xn/* s8b7 */, E(_yt/* s8eK */), _/* EXTERNAL */)),
                                _yv/* s8eS */ = function(_/* EXTERNAL */, _yw/* s8eU */){
                                  var _yx/* s8eV */ = B(_X/* FormEngine.JQuery.$wa3 */(_sG/* FormEngine.FormElement.Rendering.lvl1 */, _yw/* s8eU */, _/* EXTERNAL */)),
                                  _yy/* s8f0 */ = B(_12/* FormEngine.JQuery.$wa34 */(_yn/* s8em */, E(_yx/* s8eV */), _/* EXTERNAL */));
                                  return new F(function(){return _ui/* FormEngine.JQuery.appendT1 */(_vg/* FormEngine.FormElement.Rendering.lvl41 */, _yy/* s8f0 */, _/* EXTERNAL */);});
                                };
                                if(!B(_2n/* GHC.Base.eqString */(_ye/* s8ea */, _yn/* s8em */))){
                                  var _yz/* s8f6 */ = B(_yv/* s8eS */(_/* EXTERNAL */, E(_yu/* s8eP */)));
                                  _yh/*  s8ei */ = _yo/* s8en */;
                                  _yi/*  s8ej */ = _yz/* s8f6 */;
                                  return __continue/* EXTERNAL */;
                                }else{
                                  var _yA/* s8fb */ = B(_C/* FormEngine.JQuery.$wa20 */(_uY/* FormEngine.FormElement.Rendering.lvl23 */, _uY/* FormEngine.FormElement.Rendering.lvl23 */, E(_yu/* s8eP */), _/* EXTERNAL */)),
                                  _yB/* s8fg */ = B(_yv/* s8eS */(_/* EXTERNAL */, E(_yA/* s8fb */)));
                                  _yh/*  s8ei */ = _yo/* s8en */;
                                  _yi/*  s8ej */ = _yB/* s8fg */;
                                  return __continue/* EXTERNAL */;
                                }
                              }
                            })(_yh/*  s8ei */, _yi/*  s8ej */, _/* EXTERNAL */));
                            if(_yj/*  s8eh */!=__continue/* EXTERNAL */){
                              return _yj/*  s8eh */;
                            }
                          }
                        };
                        return new F(function(){return _yg/* s8eh */(_xN/* s8cy */, _yf/* s8ee */, _/* EXTERNAL */);});
                      }else{
                        var _yC/* s8fl */ = B(_C/* FormEngine.JQuery.$wa20 */(_uY/* FormEngine.FormElement.Rendering.lvl23 */, _uY/* FormEngine.FormElement.Rendering.lvl23 */, E(_xT/* s8d0 */), _/* EXTERNAL */)),
                        _yD/* s8fq */ = B(_xU/* s8d3 */(_/* EXTERNAL */, E(_yC/* s8fl */))),
                        _yE/* s8ft */ = function(_yF/*  s8fu */, _yG/*  s8fv */, _/* EXTERNAL */){
                          while(1){
                            var _yH/*  s8ft */ = B((function(_yI/* s8fu */, _yJ/* s8fv */, _/* EXTERNAL */){
                              var _yK/* s8fx */ = E(_yI/* s8fu */);
                              if(!_yK/* s8fx */._){
                                return _yJ/* s8fv */;
                              }else{
                                var _yL/* s8fy */ = _yK/* s8fx */.a,
                                _yM/* s8fz */ = _yK/* s8fx */.b,
                                _yN/* s8fC */ = B(_X/* FormEngine.JQuery.$wa3 */(_vd/* FormEngine.FormElement.Rendering.lvl38 */, E(_yJ/* s8fv */), _/* EXTERNAL */)),
                                _yO/* s8fH */ = B(_C/* FormEngine.JQuery.$wa20 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, _yL/* s8fy */, E(_yN/* s8fC */), _/* EXTERNAL */)),
                                _yP/* s8fM */ = B(_C/* FormEngine.JQuery.$wa20 */(_uZ/* FormEngine.FormElement.Rendering.lvl24 */, _xK/* s8ci */, E(_yO/* s8fH */), _/* EXTERNAL */)),
                                _yQ/* s8fR */ = B(_sb/* FormEngine.JQuery.$wa30 */(_wu/* s87t */, E(_yP/* s8fM */), _/* EXTERNAL */)),
                                _yR/* s8fW */ = B(_rV/* FormEngine.JQuery.$wa23 */(_wu/* s87t */, E(_yQ/* s8fR */), _/* EXTERNAL */)),
                                _yS/* s8g1 */ = B(_sr/* FormEngine.JQuery.$wa31 */(_xn/* s8b7 */, E(_yR/* s8fW */), _/* EXTERNAL */)),
                                _yT/* s8g4 */ = function(_/* EXTERNAL */, _yU/* s8g6 */){
                                  var _yV/* s8g7 */ = B(_X/* FormEngine.JQuery.$wa3 */(_sG/* FormEngine.FormElement.Rendering.lvl1 */, _yU/* s8g6 */, _/* EXTERNAL */)),
                                  _yW/* s8gc */ = B(_12/* FormEngine.JQuery.$wa34 */(_yL/* s8fy */, E(_yV/* s8g7 */), _/* EXTERNAL */));
                                  return new F(function(){return _ui/* FormEngine.JQuery.appendT1 */(_vg/* FormEngine.FormElement.Rendering.lvl41 */, _yW/* s8gc */, _/* EXTERNAL */);});
                                };
                                if(!B(_2n/* GHC.Base.eqString */(_ye/* s8ea */, _yL/* s8fy */))){
                                  var _yX/* s8gi */ = B(_yT/* s8g4 */(_/* EXTERNAL */, E(_yS/* s8g1 */)));
                                  _yF/*  s8fu */ = _yM/* s8fz */;
                                  _yG/*  s8fv */ = _yX/* s8gi */;
                                  return __continue/* EXTERNAL */;
                                }else{
                                  var _yY/* s8gn */ = B(_C/* FormEngine.JQuery.$wa20 */(_uY/* FormEngine.FormElement.Rendering.lvl23 */, _uY/* FormEngine.FormElement.Rendering.lvl23 */, E(_yS/* s8g1 */), _/* EXTERNAL */)),
                                  _yZ/* s8gs */ = B(_yT/* s8g4 */(_/* EXTERNAL */, E(_yY/* s8gn */)));
                                  _yF/*  s8fu */ = _yM/* s8fz */;
                                  _yG/*  s8fv */ = _yZ/* s8gs */;
                                  return __continue/* EXTERNAL */;
                                }
                              }
                            })(_yF/*  s8fu */, _yG/*  s8fv */, _/* EXTERNAL */));
                            if(_yH/*  s8ft */!=__continue/* EXTERNAL */){
                              return _yH/*  s8ft */;
                            }
                          }
                        };
                        return new F(function(){return _yE/* s8ft */(_xN/* s8cy */, _yD/* s8fq */, _/* EXTERNAL */);});
                      }
                    }
                  }
                  break;
                default:
                  return _xH/* s8c8 */;
              }
            }else{
              return E(_qZ/* FormEngine.FormItem.nfiUnit1 */);
            }
          },
          _z0/* s8gv */ = E(_ww/* s87w */.b);
          if(!_z0/* s8gv */._){
            var _z1/* s8gw */ = B(_u/* FormEngine.JQuery.$wa6 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, _k/* GHC.Types.[] */, _xw/* s8bE */, _/* EXTERNAL */));
            return new F(function(){return _xx/* s8bF */(_/* EXTERNAL */, _z1/* s8gw */);});
          }else{
            var _z2/* s8gB */ = B(_u/* FormEngine.JQuery.$wa6 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, B(_1R/* GHC.Show.$fShowInt_$cshow */(_z0/* s8gv */.a)), _xw/* s8bE */, _/* EXTERNAL */));
            return new F(function(){return _xx/* s8bF */(_/* EXTERNAL */, _z2/* s8gB */);});
          }
        },
        _z3/* s8gE */ = E(_xr/* s8be */.c);
        if(!_z3/* s8gE */._){
          var _z4/* s8gH */ = B(_u/* FormEngine.JQuery.$wa6 */(_v9/* FormEngine.FormElement.Rendering.lvl34 */, _k/* GHC.Types.[] */, E(_xu/* s8bz */), _/* EXTERNAL */));
          return new F(function(){return _xv/* s8bC */(_/* EXTERNAL */, E(_z4/* s8gH */));});
        }else{
          var _z5/* s8gP */ = B(_u/* FormEngine.JQuery.$wa6 */(_v9/* FormEngine.FormElement.Rendering.lvl34 */, _z3/* s8gE */.a, E(_xu/* s8bz */), _/* EXTERNAL */));
          return new F(function(){return _xv/* s8bC */(_/* EXTERNAL */, E(_z5/* s8gP */));});
        }
      };
      return new F(function(){return _to/* FormEngine.FormElement.Rendering.$wa2 */(_xp/* s8gU */, _ww/* s87w */, _wr/* s87p */, _ws/* s87q */, E(_wt/* s87r */), _/* EXTERNAL */);});
      break;
    case 5:
      var _z6/* s8gZ */ = B(_X/* FormEngine.JQuery.$wa3 */(_tj/* FormEngine.FormElement.Rendering.lvl5 */, E(_wt/* s87r */), _/* EXTERNAL */)),
      _z7/* s8h7 */ = B(_sb/* FormEngine.JQuery.$wa30 */(function(_z8/* s8h4 */, _/* EXTERNAL */){
        return new F(function(){return _t7/* FormEngine.FormElement.Rendering.a4 */(_ww/* s87w */, _/* EXTERNAL */);});
      }, E(_z6/* s8gZ */), _/* EXTERNAL */)),
      _z9/* s8hf */ = B(_sr/* FormEngine.JQuery.$wa31 */(function(_za/* s8hc */, _/* EXTERNAL */){
        return new F(function(){return _sS/* FormEngine.FormElement.Rendering.a3 */(_ww/* s87w */, _/* EXTERNAL */);});
      }, E(_z7/* s8h7 */), _/* EXTERNAL */)),
      _zb/* s8hk */ = E(_B/* FormEngine.JQuery.addClassInside_f3 */),
      _zc/* s8hn */ = __app1/* EXTERNAL */(_zb/* s8hk */, E(_z9/* s8hf */)),
      _zd/* s8hq */ = E(_A/* FormEngine.JQuery.addClassInside_f2 */),
      _ze/* s8ht */ = __app1/* EXTERNAL */(_zd/* s8hq */, _zc/* s8hn */),
      _zf/* s8hw */ = B(_X/* FormEngine.JQuery.$wa3 */(_tk/* FormEngine.FormElement.Rendering.lvl6 */, _ze/* s8ht */, _/* EXTERNAL */)),
      _zg/* s8hC */ = __app1/* EXTERNAL */(_zb/* s8hk */, E(_zf/* s8hw */)),
      _zh/* s8hG */ = __app1/* EXTERNAL */(_zd/* s8hq */, _zg/* s8hC */),
      _zi/* s8hJ */ = B(_X/* FormEngine.JQuery.$wa3 */(_tl/* FormEngine.FormElement.Rendering.lvl7 */, _zh/* s8hG */, _/* EXTERNAL */)),
      _zj/* s8hP */ = __app1/* EXTERNAL */(_zb/* s8hk */, E(_zi/* s8hJ */)),
      _zk/* s8hT */ = __app1/* EXTERNAL */(_zd/* s8hq */, _zj/* s8hP */),
      _zl/* s8hW */ = B(_X/* FormEngine.JQuery.$wa3 */(_vf/* FormEngine.FormElement.Rendering.lvl40 */, _zk/* s8hT */, _/* EXTERNAL */)),
      _zm/* s8i5 */ = B(_12/* FormEngine.JQuery.$wa34 */(new T(function(){
        var _zn/* s8i1 */ = E(_ww/* s87w */.a);
        if(_zn/* s8i1 */._==4){
          return E(_zn/* s8i1 */.b);
        }else{
          return E(_ux/* FormEngine.FormItem.ifiText1 */);
        }
      },1), E(_zl/* s8hW */), _/* EXTERNAL */)),
      _zo/* s8ia */ = E(_z/* FormEngine.JQuery.addClassInside_f1 */),
      _zp/* s8id */ = __app1/* EXTERNAL */(_zo/* s8ia */, E(_zm/* s8i5 */)),
      _zq/* s8ih */ = __app1/* EXTERNAL */(_zo/* s8ia */, _zp/* s8id */),
      _zr/* s8il */ = __app1/* EXTERNAL */(_zo/* s8ia */, _zq/* s8ih */);
      return new F(function(){return _sB/* FormEngine.FormElement.Rendering.a1 */(_ww/* s87w */, _zr/* s8il */, _/* EXTERNAL */);});
      break;
    case 6:
      var _zs/* s8ip */ = _ww/* s87w */.a,
      _zt/* s8iq */ = _ww/* s87w */.b,
      _zu/* s8is */ = new T(function(){
        return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_zs/* s8ip */)).b));
      }),
      _zv/* s8iH */ = new T(function(){
        var _zw/* s8iU */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_zs/* s8ip */)).c);
        if(!_zw/* s8iU */._){
          return __Z/* EXTERNAL */;
        }else{
          return E(_zw/* s8iU */.a);
        }
      }),
      _zx/* s8iW */ = function(_zy/* s8iX */, _/* EXTERNAL */){
        var _zz/* s8iZ */ = B(_uA/* FormEngine.JQuery.isRadioSelected1 */(_zu/* s8is */, _/* EXTERNAL */));
        return new F(function(){return _pM/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_ww/* s87w */, _wr/* s87p */, _zz/* s8iZ */, _/* EXTERNAL */);});
      },
      _zA/* s8j2 */ = new T(function(){
        return B(_ut/* FormEngine.FormElement.Rendering.go */(_zt/* s8iq */, _uL/* GHC.List.last1 */));
      }),
      _zB/* s8j3 */ = function(_zC/* s8j4 */, _/* EXTERNAL */){
        return new F(function(){return _2E/* FormEngine.JQuery.select1 */(B(_7/* GHC.Base.++ */(_uX/* FormEngine.FormElement.Rendering.lvl22 */, new T(function(){
          return B(_7/* GHC.Base.++ */(B(_wh/* FormEngine.FormElement.Identifiers.radioId */(_ww/* s87w */, _zC/* s8j4 */)), _vX/* FormEngine.FormElement.Identifiers.optionSectionId1 */));
        },1))), _/* EXTERNAL */);});
      },
      _zD/* s8j9 */ = function(_zE/* s8ja */, _/* EXTERNAL */){
        while(1){
          var _zF/* s8jc */ = E(_zE/* s8ja */);
          if(!_zF/* s8jc */._){
            return _k/* GHC.Types.[] */;
          }else{
            var _zG/* s8je */ = _zF/* s8jc */.b,
            _zH/* s8jf */ = E(_zF/* s8jc */.a);
            if(!_zH/* s8jf */._){
              _zE/* s8ja */ = _zG/* s8je */;
              continue;
            }else{
              var _zI/* s8jl */ = B(_zB/* s8j3 */(_zH/* s8jf */, _/* EXTERNAL */)),
              _zJ/* s8jo */ = B(_zD/* s8j9 */(_zG/* s8je */, _/* EXTERNAL */));
              return new T2(1,_zI/* s8jl */,_zJ/* s8jo */);
            }
          }
        }
      },
      _zK/* s8m1 */ = function(_/* EXTERNAL */){
        var _zL/* s8jt */ = B(_2E/* FormEngine.JQuery.select1 */(_ve/* FormEngine.FormElement.Rendering.lvl39 */, _/* EXTERNAL */)),
        _zM/* s8jw */ = function(_zN/*  s8jx */, _zO/*  s8jy */, _/* EXTERNAL */){
          while(1){
            var _zP/*  s8jw */ = B((function(_zQ/* s8jx */, _zR/* s8jy */, _/* EXTERNAL */){
              var _zS/* s8jA */ = E(_zQ/* s8jx */);
              if(!_zS/* s8jA */._){
                return _zR/* s8jy */;
              }else{
                var _zT/* s8jB */ = _zS/* s8jA */.a,
                _zU/* s8jC */ = _zS/* s8jA */.b,
                _zV/* s8jF */ = B(_X/* FormEngine.JQuery.$wa3 */(_vd/* FormEngine.FormElement.Rendering.lvl38 */, E(_zR/* s8jy */), _/* EXTERNAL */)),
                _zW/* s8jL */ = B(_C/* FormEngine.JQuery.$wa20 */(_ti/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                  return B(_wh/* FormEngine.FormElement.Identifiers.radioId */(_ww/* s87w */, _zT/* s8jB */));
                },1), E(_zV/* s8jF */), _/* EXTERNAL */)),
                _zX/* s8jQ */ = B(_C/* FormEngine.JQuery.$wa20 */(_uZ/* FormEngine.FormElement.Rendering.lvl24 */, _zu/* s8is */, E(_zW/* s8jL */), _/* EXTERNAL */)),
                _zY/* s8jV */ = B(_C/* FormEngine.JQuery.$wa20 */(_v9/* FormEngine.FormElement.Rendering.lvl34 */, _zv/* s8iH */, E(_zX/* s8jQ */), _/* EXTERNAL */)),
                _zZ/* s8k1 */ = B(_C/* FormEngine.JQuery.$wa20 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, new T(function(){
                  return B(_vS/* FormEngine.FormElement.FormElement.optionElemValue */(_zT/* s8jB */));
                },1), E(_zY/* s8jV */), _/* EXTERNAL */)),
                _A0/* s8k4 */ = function(_/* EXTERNAL */, _A1/* s8k6 */){
                  var _A2/* s8kA */ = B(_rV/* FormEngine.JQuery.$wa23 */(function(_A3/* s8k7 */, _/* EXTERNAL */){
                    var _A4/* s8k9 */ = B(_zD/* s8j9 */(_zt/* s8iq */, _/* EXTERNAL */)),
                    _A5/* s8kc */ = B(_ue/* FormEngine.FormElement.Rendering.a5 */(_A4/* s8k9 */, _/* EXTERNAL */)),
                    _A6/* s8kf */ = E(_zT/* s8jB */);
                    if(!_A6/* s8kf */._){
                      var _A7/* s8ki */ = B(_uA/* FormEngine.JQuery.isRadioSelected1 */(_zu/* s8is */, _/* EXTERNAL */));
                      return new F(function(){return _pM/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_ww/* s87w */, _wr/* s87p */, _A7/* s8ki */, _/* EXTERNAL */);});
                    }else{
                      var _A8/* s8ko */ = B(_zB/* s8j3 */(_A6/* s8kf */, _/* EXTERNAL */)),
                      _A9/* s8kt */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2l/* FormEngine.JQuery.appearJq2 */, E(_A8/* s8ko */), _/* EXTERNAL */)),
                      _Aa/* s8kw */ = B(_uA/* FormEngine.JQuery.isRadioSelected1 */(_zu/* s8is */, _/* EXTERNAL */));
                      return new F(function(){return _pM/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_ww/* s87w */, _wr/* s87p */, _Aa/* s8kw */, _/* EXTERNAL */);});
                    }
                  }, _A1/* s8k6 */, _/* EXTERNAL */)),
                  _Ab/* s8kF */ = B(_sr/* FormEngine.JQuery.$wa31 */(_zx/* s8iW */, E(_A2/* s8kA */), _/* EXTERNAL */)),
                  _Ac/* s8kK */ = B(_X/* FormEngine.JQuery.$wa3 */(_sG/* FormEngine.FormElement.Rendering.lvl1 */, E(_Ab/* s8kF */), _/* EXTERNAL */)),
                  _Ad/* s8kQ */ = B(_12/* FormEngine.JQuery.$wa34 */(new T(function(){
                    return B(_vS/* FormEngine.FormElement.FormElement.optionElemValue */(_zT/* s8jB */));
                  },1), E(_Ac/* s8kK */), _/* EXTERNAL */)),
                  _Ae/* s8kT */ = E(_zT/* s8jB */);
                  if(!_Ae/* s8kT */._){
                    var _Af/* s8kU */ = _Ae/* s8kT */.a,
                    _Ag/* s8kY */ = B(_X/* FormEngine.JQuery.$wa3 */(_k/* GHC.Types.[] */, E(_Ad/* s8kQ */), _/* EXTERNAL */)),
                    _Ah/* s8l1 */ = E(_zA/* s8j2 */);
                    if(!_Ah/* s8l1 */._){
                      if(!B(_4T/* FormEngine.FormItem.$fEqOption_$c== */(_Af/* s8kU */, _Ah/* s8l1 */.a))){
                        return new F(function(){return _ui/* FormEngine.JQuery.appendT1 */(_vc/* FormEngine.FormElement.Rendering.lvl37 */, _Ag/* s8kY */, _/* EXTERNAL */);});
                      }else{
                        return _Ag/* s8kY */;
                      }
                    }else{
                      if(!B(_4T/* FormEngine.FormItem.$fEqOption_$c== */(_Af/* s8kU */, _Ah/* s8l1 */.a))){
                        return new F(function(){return _ui/* FormEngine.JQuery.appendT1 */(_vc/* FormEngine.FormElement.Rendering.lvl37 */, _Ag/* s8kY */, _/* EXTERNAL */);});
                      }else{
                        return _Ag/* s8kY */;
                      }
                    }
                  }else{
                    var _Ai/* s8l9 */ = _Ae/* s8kT */.a,
                    _Aj/* s8le */ = B(_X/* FormEngine.JQuery.$wa3 */(_uW/* FormEngine.FormElement.Rendering.lvl21 */, E(_Ad/* s8kQ */), _/* EXTERNAL */)),
                    _Ak/* s8lh */ = E(_zA/* s8j2 */);
                    if(!_Ak/* s8lh */._){
                      if(!B(_4T/* FormEngine.FormItem.$fEqOption_$c== */(_Ai/* s8l9 */, _Ak/* s8lh */.a))){
                        return new F(function(){return _ui/* FormEngine.JQuery.appendT1 */(_vc/* FormEngine.FormElement.Rendering.lvl37 */, _Aj/* s8le */, _/* EXTERNAL */);});
                      }else{
                        return _Aj/* s8le */;
                      }
                    }else{
                      if(!B(_4T/* FormEngine.FormItem.$fEqOption_$c== */(_Ai/* s8l9 */, _Ak/* s8lh */.a))){
                        return new F(function(){return _ui/* FormEngine.JQuery.appendT1 */(_vc/* FormEngine.FormElement.Rendering.lvl37 */, _Aj/* s8le */, _/* EXTERNAL */);});
                      }else{
                        return _Aj/* s8le */;
                      }
                    }
                  }
                },
                _Al/* s8lp */ = E(_zT/* s8jB */);
                if(!_Al/* s8lp */._){
                  if(!E(_Al/* s8lp */.b)){
                    var _Am/* s8lv */ = B(_A0/* s8k4 */(_/* EXTERNAL */, E(_zZ/* s8k1 */)));
                    _zN/*  s8jx */ = _zU/* s8jC */;
                    _zO/*  s8jy */ = _Am/* s8lv */;
                    return __continue/* EXTERNAL */;
                  }else{
                    var _An/* s8lA */ = B(_C/* FormEngine.JQuery.$wa20 */(_uY/* FormEngine.FormElement.Rendering.lvl23 */, _uY/* FormEngine.FormElement.Rendering.lvl23 */, E(_zZ/* s8k1 */), _/* EXTERNAL */)),
                    _Ao/* s8lF */ = B(_A0/* s8k4 */(_/* EXTERNAL */, E(_An/* s8lA */)));
                    _zN/*  s8jx */ = _zU/* s8jC */;
                    _zO/*  s8jy */ = _Ao/* s8lF */;
                    return __continue/* EXTERNAL */;
                  }
                }else{
                  if(!E(_Al/* s8lp */.b)){
                    var _Ap/* s8lO */ = B(_A0/* s8k4 */(_/* EXTERNAL */, E(_zZ/* s8k1 */)));
                    _zN/*  s8jx */ = _zU/* s8jC */;
                    _zO/*  s8jy */ = _Ap/* s8lO */;
                    return __continue/* EXTERNAL */;
                  }else{
                    var _Aq/* s8lT */ = B(_C/* FormEngine.JQuery.$wa20 */(_uY/* FormEngine.FormElement.Rendering.lvl23 */, _uY/* FormEngine.FormElement.Rendering.lvl23 */, E(_zZ/* s8k1 */), _/* EXTERNAL */)),
                    _Ar/* s8lY */ = B(_A0/* s8k4 */(_/* EXTERNAL */, E(_Aq/* s8lT */)));
                    _zN/*  s8jx */ = _zU/* s8jC */;
                    _zO/*  s8jy */ = _Ar/* s8lY */;
                    return __continue/* EXTERNAL */;
                  }
                }
              }
            })(_zN/*  s8jx */, _zO/*  s8jy */, _/* EXTERNAL */));
            if(_zP/*  s8jw */!=__continue/* EXTERNAL */){
              return _zP/*  s8jw */;
            }
          }
        };
        return new F(function(){return _zM/* s8jw */(_zt/* s8iq */, _zL/* s8jt */, _/* EXTERNAL */);});
      },
      _As/* s8m2 */ = B(_to/* FormEngine.FormElement.Rendering.$wa2 */(_zK/* s8m1 */, _ww/* s87w */, _wr/* s87p */, _ws/* s87q */, E(_wt/* s87r */), _/* EXTERNAL */)),
      _At/* s8m5 */ = function(_Au/* s8m6 */, _Av/* s8m7 */, _/* EXTERNAL */){
        while(1){
          var _Aw/* s8m9 */ = E(_Au/* s8m6 */);
          if(!_Aw/* s8m9 */._){
            return _Av/* s8m7 */;
          }else{
            var _Ax/* s8mc */ = B(_wp/* FormEngine.FormElement.Rendering.foldElements2 */(_Aw/* s8m9 */.a, _wr/* s87p */, _ws/* s87q */, _Av/* s8m7 */, _/* EXTERNAL */));
            _Au/* s8m6 */ = _Aw/* s8m9 */.b;
            _Av/* s8m7 */ = _Ax/* s8mc */;
            continue;
          }
        }
      },
      _Ay/* s8mf */ = function(_Az/*  s8mg */, _AA/*  s8mh */, _/* EXTERNAL */){
        while(1){
          var _AB/*  s8mf */ = B((function(_AC/* s8mg */, _AD/* s8mh */, _/* EXTERNAL */){
            var _AE/* s8mj */ = E(_AC/* s8mg */);
            if(!_AE/* s8mj */._){
              return _AD/* s8mh */;
            }else{
              var _AF/* s8ml */ = _AE/* s8mj */.b,
              _AG/* s8mm */ = E(_AE/* s8mj */.a);
              if(!_AG/* s8mm */._){
                var _AH/*   s8mh */ = _AD/* s8mh */;
                _Az/*  s8mg */ = _AF/* s8ml */;
                _AA/*  s8mh */ = _AH/*   s8mh */;
                return __continue/* EXTERNAL */;
              }else{
                var _AI/* s8mu */ = B(_X/* FormEngine.JQuery.$wa3 */(_vb/* FormEngine.FormElement.Rendering.lvl36 */, E(_AD/* s8mh */), _/* EXTERNAL */)),
                _AJ/* s8mB */ = B(_C/* FormEngine.JQuery.$wa20 */(_ti/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                  return B(_7/* GHC.Base.++ */(B(_wh/* FormEngine.FormElement.Identifiers.radioId */(_ww/* s87w */, _AG/* s8mm */)), _vX/* FormEngine.FormElement.Identifiers.optionSectionId1 */));
                },1), E(_AI/* s8mu */), _/* EXTERNAL */)),
                _AK/* s8mG */ = E(_B/* FormEngine.JQuery.addClassInside_f3 */),
                _AL/* s8mJ */ = __app1/* EXTERNAL */(_AK/* s8mG */, E(_AJ/* s8mB */)),
                _AM/* s8mM */ = E(_A/* FormEngine.JQuery.addClassInside_f2 */),
                _AN/* s8mP */ = __app1/* EXTERNAL */(_AM/* s8mM */, _AL/* s8mJ */),
                _AO/* s8mS */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2X/* FormEngine.JQuery.disappearJq2 */, _AN/* s8mP */, _/* EXTERNAL */)),
                _AP/* s8mV */ = B(_At/* s8m5 */(_AG/* s8mm */.c, _AO/* s8mS */, _/* EXTERNAL */)),
                _AQ/* s8n0 */ = E(_z/* FormEngine.JQuery.addClassInside_f1 */),
                _AR/* s8n3 */ = __app1/* EXTERNAL */(_AQ/* s8n0 */, E(_AP/* s8mV */)),
                _AS/* s8n6 */ = function(_AT/*  s8n7 */, _AU/*  s8n8 */, _AV/*  s7kM */, _/* EXTERNAL */){
                  while(1){
                    var _AW/*  s8n6 */ = B((function(_AX/* s8n7 */, _AY/* s8n8 */, _AZ/* s7kM */, _/* EXTERNAL */){
                      var _B0/* s8na */ = E(_AX/* s8n7 */);
                      if(!_B0/* s8na */._){
                        return _AY/* s8n8 */;
                      }else{
                        var _B1/* s8nd */ = _B0/* s8na */.b,
                        _B2/* s8ne */ = E(_B0/* s8na */.a);
                        if(!_B2/* s8ne */._){
                          var _B3/*   s8n8 */ = _AY/* s8n8 */,
                          _B4/*   s7kM */ = _/* EXTERNAL */;
                          _AT/*  s8n7 */ = _B1/* s8nd */;
                          _AU/*  s8n8 */ = _B3/*   s8n8 */;
                          _AV/*  s7kM */ = _B4/*   s7kM */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _B5/* s8nk */ = B(_X/* FormEngine.JQuery.$wa3 */(_vb/* FormEngine.FormElement.Rendering.lvl36 */, _AY/* s8n8 */, _/* EXTERNAL */)),
                          _B6/* s8nr */ = B(_C/* FormEngine.JQuery.$wa20 */(_ti/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                            return B(_7/* GHC.Base.++ */(B(_wh/* FormEngine.FormElement.Identifiers.radioId */(_ww/* s87w */, _B2/* s8ne */)), _vX/* FormEngine.FormElement.Identifiers.optionSectionId1 */));
                          },1), E(_B5/* s8nk */), _/* EXTERNAL */)),
                          _B7/* s8nx */ = __app1/* EXTERNAL */(_AK/* s8mG */, E(_B6/* s8nr */)),
                          _B8/* s8nB */ = __app1/* EXTERNAL */(_AM/* s8mM */, _B7/* s8nx */),
                          _B9/* s8nE */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2X/* FormEngine.JQuery.disappearJq2 */, _B8/* s8nB */, _/* EXTERNAL */)),
                          _Ba/* s8nH */ = B(_At/* s8m5 */(_B2/* s8ne */.c, _B9/* s8nE */, _/* EXTERNAL */)),
                          _Bb/* s8nN */ = __app1/* EXTERNAL */(_AQ/* s8n0 */, E(_Ba/* s8nH */)),
                          _B4/*   s7kM */ = _/* EXTERNAL */;
                          _AT/*  s8n7 */ = _B1/* s8nd */;
                          _AU/*  s8n8 */ = _Bb/* s8nN */;
                          _AV/*  s7kM */ = _B4/*   s7kM */;
                          return __continue/* EXTERNAL */;
                        }
                      }
                    })(_AT/*  s8n7 */, _AU/*  s8n8 */, _AV/*  s7kM */, _/* EXTERNAL */));
                    if(_AW/*  s8n6 */!=__continue/* EXTERNAL */){
                      return _AW/*  s8n6 */;
                    }
                  }
                };
                return new F(function(){return _AS/* s8n6 */(_AF/* s8ml */, _AR/* s8n3 */, _/* EXTERNAL */, _/* EXTERNAL */);});
              }
            }
          })(_Az/*  s8mg */, _AA/*  s8mh */, _/* EXTERNAL */));
          if(_AB/*  s8mf */!=__continue/* EXTERNAL */){
            return _AB/*  s8mf */;
          }
        }
      };
      return new F(function(){return _Ay/* s8mf */(_zt/* s8iq */, _As/* s8m2 */, _/* EXTERNAL */);});
      break;
    case 7:
      var _Bc/* s8nQ */ = _ww/* s87w */.a,
      _Bd/* s8qK */ = function(_/* EXTERNAL */){
        var _Be/* s8nW */ = B(_2E/* FormEngine.JQuery.select1 */(_va/* FormEngine.FormElement.Rendering.lvl35 */, _/* EXTERNAL */)),
        _Bf/* s8nZ */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(_Bc/* s8nQ */)),
        _Bg/* s8oe */ = B(_u/* FormEngine.JQuery.$wa6 */(_uZ/* FormEngine.FormElement.Rendering.lvl24 */, B(_27/* FormEngine.FormItem.numbering2text */(_Bf/* s8nZ */.b)), E(_Be/* s8nW */), _/* EXTERNAL */)),
        _Bh/* s8oh */ = function(_/* EXTERNAL */, _Bi/* s8oj */){
          var _Bj/* s8on */ = B(_vp/* FormEngine.JQuery.onBlur1 */(function(_Bk/* s8ok */, _/* EXTERNAL */){
            return new F(function(){return _rG/* FormEngine.FormElement.Rendering.$wa1 */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
          }, _Bi/* s8oj */, _/* EXTERNAL */)),
          _Bl/* s8ot */ = B(_vz/* FormEngine.JQuery.onChange1 */(function(_Bm/* s8oq */, _/* EXTERNAL */){
            return new F(function(){return _rG/* FormEngine.FormElement.Rendering.$wa1 */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
          }, _Bj/* s8on */, _/* EXTERNAL */)),
          _Bn/* s8oz */ = B(_si/* FormEngine.JQuery.onMouseLeave1 */(function(_Bo/* s8ow */, _/* EXTERNAL */){
            return new F(function(){return _ry/* FormEngine.FormElement.Rendering.$wa */(_ww/* s87w */, _wr/* s87p */, _ws/* s87q */, _/* EXTERNAL */);});
          }, _Bl/* s8ot */, _/* EXTERNAL */)),
          _Bp/* s8oC */ = E(_Bc/* s8nQ */);
          if(_Bp/* s8oC */._==6){
            var _Bq/* s8oG */ = E(_Bp/* s8oC */.b);
            if(!_Bq/* s8oG */._){
              return _Bn/* s8oz */;
            }else{
              var _Br/* s8oI */ = _Bq/* s8oG */.b,
              _Bs/* s8oJ */ = E(_Bq/* s8oG */.a),
              _Bt/* s8oK */ = _Bs/* s8oJ */.a,
              _Bu/* s8oO */ = B(_X/* FormEngine.JQuery.$wa3 */(_v8/* FormEngine.FormElement.Rendering.lvl33 */, E(_Bn/* s8oz */), _/* EXTERNAL */)),
              _Bv/* s8oT */ = B(_C/* FormEngine.JQuery.$wa20 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, _Bt/* s8oK */, E(_Bu/* s8oO */), _/* EXTERNAL */)),
              _Bw/* s8oY */ = B(_12/* FormEngine.JQuery.$wa34 */(_Bs/* s8oJ */.b, E(_Bv/* s8oT */), _/* EXTERNAL */)),
              _Bx/* s8p1 */ = E(_ww/* s87w */.b);
              if(!_Bx/* s8p1 */._){
                var _By/* s8p2 */ = function(_Bz/* s8p3 */, _BA/* s8p4 */, _/* EXTERNAL */){
                  while(1){
                    var _BB/* s8p6 */ = E(_Bz/* s8p3 */);
                    if(!_BB/* s8p6 */._){
                      return _BA/* s8p4 */;
                    }else{
                      var _BC/* s8p9 */ = E(_BB/* s8p6 */.a),
                      _BD/* s8pe */ = B(_X/* FormEngine.JQuery.$wa3 */(_v8/* FormEngine.FormElement.Rendering.lvl33 */, E(_BA/* s8p4 */), _/* EXTERNAL */)),
                      _BE/* s8pj */ = B(_C/* FormEngine.JQuery.$wa20 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, _BC/* s8p9 */.a, E(_BD/* s8pe */), _/* EXTERNAL */)),
                      _BF/* s8po */ = B(_12/* FormEngine.JQuery.$wa34 */(_BC/* s8p9 */.b, E(_BE/* s8pj */), _/* EXTERNAL */));
                      _Bz/* s8p3 */ = _BB/* s8p6 */.b;
                      _BA/* s8p4 */ = _BF/* s8po */;
                      continue;
                    }
                  }
                };
                return new F(function(){return _By/* s8p2 */(_Br/* s8oI */, _Bw/* s8oY */, _/* EXTERNAL */);});
              }else{
                var _BG/* s8pr */ = _Bx/* s8p1 */.a;
                if(!B(_2n/* GHC.Base.eqString */(_Bt/* s8oK */, _BG/* s8pr */))){
                  var _BH/* s8pt */ = function(_BI/* s8pu */, _BJ/* s8pv */, _/* EXTERNAL */){
                    while(1){
                      var _BK/* s8px */ = E(_BI/* s8pu */);
                      if(!_BK/* s8px */._){
                        return _BJ/* s8pv */;
                      }else{
                        var _BL/* s8pz */ = _BK/* s8px */.b,
                        _BM/* s8pA */ = E(_BK/* s8px */.a),
                        _BN/* s8pB */ = _BM/* s8pA */.a,
                        _BO/* s8pF */ = B(_X/* FormEngine.JQuery.$wa3 */(_v8/* FormEngine.FormElement.Rendering.lvl33 */, E(_BJ/* s8pv */), _/* EXTERNAL */)),
                        _BP/* s8pK */ = B(_C/* FormEngine.JQuery.$wa20 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, _BN/* s8pB */, E(_BO/* s8pF */), _/* EXTERNAL */)),
                        _BQ/* s8pP */ = B(_12/* FormEngine.JQuery.$wa34 */(_BM/* s8pA */.b, E(_BP/* s8pK */), _/* EXTERNAL */));
                        if(!B(_2n/* GHC.Base.eqString */(_BN/* s8pB */, _BG/* s8pr */))){
                          _BI/* s8pu */ = _BL/* s8pz */;
                          _BJ/* s8pv */ = _BQ/* s8pP */;
                          continue;
                        }else{
                          var _BR/* s8pV */ = B(_C/* FormEngine.JQuery.$wa20 */(_v7/* FormEngine.FormElement.Rendering.lvl32 */, _v7/* FormEngine.FormElement.Rendering.lvl32 */, E(_BQ/* s8pP */), _/* EXTERNAL */));
                          _BI/* s8pu */ = _BL/* s8pz */;
                          _BJ/* s8pv */ = _BR/* s8pV */;
                          continue;
                        }
                      }
                    }
                  };
                  return new F(function(){return _BH/* s8pt */(_Br/* s8oI */, _Bw/* s8oY */, _/* EXTERNAL */);});
                }else{
                  var _BS/* s8q0 */ = B(_C/* FormEngine.JQuery.$wa20 */(_v7/* FormEngine.FormElement.Rendering.lvl32 */, _v7/* FormEngine.FormElement.Rendering.lvl32 */, E(_Bw/* s8oY */), _/* EXTERNAL */)),
                  _BT/* s8q3 */ = function(_BU/* s8q4 */, _BV/* s8q5 */, _/* EXTERNAL */){
                    while(1){
                      var _BW/* s8q7 */ = E(_BU/* s8q4 */);
                      if(!_BW/* s8q7 */._){
                        return _BV/* s8q5 */;
                      }else{
                        var _BX/* s8q9 */ = _BW/* s8q7 */.b,
                        _BY/* s8qa */ = E(_BW/* s8q7 */.a),
                        _BZ/* s8qb */ = _BY/* s8qa */.a,
                        _C0/* s8qf */ = B(_X/* FormEngine.JQuery.$wa3 */(_v8/* FormEngine.FormElement.Rendering.lvl33 */, E(_BV/* s8q5 */), _/* EXTERNAL */)),
                        _C1/* s8qk */ = B(_C/* FormEngine.JQuery.$wa20 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, _BZ/* s8qb */, E(_C0/* s8qf */), _/* EXTERNAL */)),
                        _C2/* s8qp */ = B(_12/* FormEngine.JQuery.$wa34 */(_BY/* s8qa */.b, E(_C1/* s8qk */), _/* EXTERNAL */));
                        if(!B(_2n/* GHC.Base.eqString */(_BZ/* s8qb */, _BG/* s8pr */))){
                          _BU/* s8q4 */ = _BX/* s8q9 */;
                          _BV/* s8q5 */ = _C2/* s8qp */;
                          continue;
                        }else{
                          var _C3/* s8qv */ = B(_C/* FormEngine.JQuery.$wa20 */(_v7/* FormEngine.FormElement.Rendering.lvl32 */, _v7/* FormEngine.FormElement.Rendering.lvl32 */, E(_C2/* s8qp */), _/* EXTERNAL */));
                          _BU/* s8q4 */ = _BX/* s8q9 */;
                          _BV/* s8q5 */ = _C3/* s8qv */;
                          continue;
                        }
                      }
                    }
                  };
                  return new F(function(){return _BT/* s8q3 */(_Br/* s8oI */, _BS/* s8q0 */, _/* EXTERNAL */);});
                }
              }
            }
          }else{
            return E(_uM/* FormEngine.FormItem.lfiAvailableOptions1 */);
          }
        },
        _C4/* s8qy */ = E(_Bf/* s8nZ */.c);
        if(!_C4/* s8qy */._){
          var _C5/* s8qB */ = B(_u/* FormEngine.JQuery.$wa6 */(_v9/* FormEngine.FormElement.Rendering.lvl34 */, _k/* GHC.Types.[] */, E(_Bg/* s8oe */), _/* EXTERNAL */));
          return new F(function(){return _Bh/* s8oh */(_/* EXTERNAL */, _C5/* s8qB */);});
        }else{
          var _C6/* s8qH */ = B(_u/* FormEngine.JQuery.$wa6 */(_v9/* FormEngine.FormElement.Rendering.lvl34 */, _C4/* s8qy */.a, E(_Bg/* s8oe */), _/* EXTERNAL */));
          return new F(function(){return _Bh/* s8oh */(_/* EXTERNAL */, _C6/* s8qH */);});
        }
      };
      return new F(function(){return _to/* FormEngine.FormElement.Rendering.$wa2 */(_Bd/* s8qK */, _ww/* s87w */, _wr/* s87p */, _ws/* s87q */, E(_wt/* s87r */), _/* EXTERNAL */);});
      break;
    case 8:
      var _C7/* s8qL */ = _ww/* s87w */.a,
      _C8/* s8qM */ = _ww/* s87w */.b,
      _C9/* s8qQ */ = B(_X/* FormEngine.JQuery.$wa3 */(_v6/* FormEngine.FormElement.Rendering.lvl31 */, E(_wt/* s87r */), _/* EXTERNAL */)),
      _Ca/* s8qV */ = new T(function(){
        var _Cb/* s8qW */ = E(_C7/* s8qL */);
        switch(_Cb/* s8qW */._){
          case 8:
            return E(_Cb/* s8qW */.b);
            break;
          case 9:
            return E(_Cb/* s8qW */.b);
            break;
          case 10:
            return E(_Cb/* s8qW */.b);
            break;
          default:
            return E(_51/* FormEngine.FormItem.$fShowNumbering2 */);
        }
      }),
      _Cc/* s8r7 */ = B(_C/* FormEngine.JQuery.$wa20 */(_v1/* FormEngine.FormElement.Rendering.lvl26 */, new T(function(){
        return B(_1R/* GHC.Show.$fShowInt_$cshow */(_Ca/* s8qV */));
      },1), E(_C9/* s8qQ */), _/* EXTERNAL */)),
      _Cd/* s8ra */ = E(_Ca/* s8qV */),
      _Ce/* s8rc */ = function(_/* EXTERNAL */, _Cf/* s8re */){
        var _Cg/* s8ri */ = __app1/* EXTERNAL */(E(_B/* FormEngine.JQuery.addClassInside_f3 */), _Cf/* s8re */),
        _Ch/* s8ro */ = __app1/* EXTERNAL */(E(_A/* FormEngine.JQuery.addClassInside_f2 */), _Cg/* s8ri */),
        _Ci/* s8rr */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(_C7/* s8qL */)),
        _Cj/* s8rw */ = _Ci/* s8rr */.e,
        _Ck/* s8rD */ = E(_Ci/* s8rr */.a);
        if(!_Ck/* s8rD */._){
          var _Cl/* s8rE */ = function(_/* EXTERNAL */, _Cm/* s8rG */){
            var _Cn/* s8rH */ = function(_Co/* s8rI */, _Cp/* s8rJ */, _/* EXTERNAL */){
              while(1){
                var _Cq/* s8rL */ = E(_Co/* s8rI */);
                if(!_Cq/* s8rL */._){
                  return _Cp/* s8rJ */;
                }else{
                  var _Cr/* s8rO */ = B(_wp/* FormEngine.FormElement.Rendering.foldElements2 */(_Cq/* s8rL */.a, _wr/* s87p */, _ws/* s87q */, _Cp/* s8rJ */, _/* EXTERNAL */));
                  _Co/* s8rI */ = _Cq/* s8rL */.b;
                  _Cp/* s8rJ */ = _Cr/* s8rO */;
                  continue;
                }
              }
            },
            _Cs/* s8rR */ = B(_Cn/* s8rH */(_C8/* s8qM */, _Cm/* s8rG */, _/* EXTERNAL */));
            return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_Cs/* s8rR */));});
          },
          _Ct/* s8s3 */ = E(_Cj/* s8rw */);
          if(!_Ct/* s8s3 */._){
            return new F(function(){return _Cl/* s8rE */(_/* EXTERNAL */, _Ch/* s8ro */);});
          }else{
            var _Cu/* s8s6 */ = B(_X/* FormEngine.JQuery.$wa3 */(_sx/* FormEngine.FormElement.Rendering.lvl */, _Ch/* s8ro */, _/* EXTERNAL */)),
            _Cv/* s8sb */ = B(_12/* FormEngine.JQuery.$wa34 */(_Ct/* s8s3 */.a, E(_Cu/* s8s6 */), _/* EXTERNAL */));
            return new F(function(){return _Cl/* s8rE */(_/* EXTERNAL */, _Cv/* s8sb */);});
          }
        }else{
          var _Cw/* s8si */ = B(_X/* FormEngine.JQuery.$wa3 */(B(_7/* GHC.Base.++ */(_v4/* FormEngine.FormElement.Rendering.lvl29 */, new T(function(){
            return B(_7/* GHC.Base.++ */(B(_1M/* GHC.Show.$wshowSignedInt */(0, _Cd/* s8ra */, _k/* GHC.Types.[] */)), _v3/* FormEngine.FormElement.Rendering.lvl28 */));
          },1))), _Ch/* s8ro */, _/* EXTERNAL */)),
          _Cx/* s8sn */ = B(_12/* FormEngine.JQuery.$wa34 */(_Ck/* s8rD */.a, E(_Cw/* s8si */), _/* EXTERNAL */)),
          _Cy/* s8sq */ = function(_/* EXTERNAL */, _Cz/* s8ss */){
            var _CA/* s8st */ = function(_CB/* s8su */, _CC/* s8sv */, _/* EXTERNAL */){
              while(1){
                var _CD/* s8sx */ = E(_CB/* s8su */);
                if(!_CD/* s8sx */._){
                  return _CC/* s8sv */;
                }else{
                  var _CE/* s8sA */ = B(_wp/* FormEngine.FormElement.Rendering.foldElements2 */(_CD/* s8sx */.a, _wr/* s87p */, _ws/* s87q */, _CC/* s8sv */, _/* EXTERNAL */));
                  _CB/* s8su */ = _CD/* s8sx */.b;
                  _CC/* s8sv */ = _CE/* s8sA */;
                  continue;
                }
              }
            },
            _CF/* s8sD */ = B(_CA/* s8st */(_C8/* s8qM */, _Cz/* s8ss */, _/* EXTERNAL */));
            return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), E(_CF/* s8sD */));});
          },
          _CG/* s8sP */ = E(_Cj/* s8rw */);
          if(!_CG/* s8sP */._){
            return new F(function(){return _Cy/* s8sq */(_/* EXTERNAL */, _Cx/* s8sn */);});
          }else{
            var _CH/* s8sT */ = B(_X/* FormEngine.JQuery.$wa3 */(_sx/* FormEngine.FormElement.Rendering.lvl */, E(_Cx/* s8sn */), _/* EXTERNAL */)),
            _CI/* s8sY */ = B(_12/* FormEngine.JQuery.$wa34 */(_CG/* s8sP */.a, E(_CH/* s8sT */), _/* EXTERNAL */));
            return new F(function(){return _Cy/* s8sq */(_/* EXTERNAL */, _CI/* s8sY */);});
          }
        }
      };
      if(_Cd/* s8ra */<=1){
        return new F(function(){return _Ce/* s8rc */(_/* EXTERNAL */, E(_Cc/* s8r7 */));});
      }else{
        var _CJ/* s8t7 */ = B(_rO/* FormEngine.JQuery.$wa1 */(_v5/* FormEngine.FormElement.Rendering.lvl30 */, E(_Cc/* s8r7 */), _/* EXTERNAL */));
        return new F(function(){return _Ce/* s8rc */(_/* EXTERNAL */, E(_CJ/* s8t7 */));});
      }
      break;
    case 9:
      var _CK/* s8tc */ = _ww/* s87w */.a,
      _CL/* s8te */ = _ww/* s87w */.c,
      _CM/* s8ti */ = B(_X/* FormEngine.JQuery.$wa3 */(_v2/* FormEngine.FormElement.Rendering.lvl27 */, E(_wt/* s87r */), _/* EXTERNAL */)),
      _CN/* s8tE */ = B(_C/* FormEngine.JQuery.$wa20 */(_v1/* FormEngine.FormElement.Rendering.lvl26 */, new T(function(){
        var _CO/* s8tn */ = E(_CK/* s8tc */);
        switch(_CO/* s8tn */._){
          case 8:
            return B(_1M/* GHC.Show.$wshowSignedInt */(0, E(_CO/* s8tn */.b), _k/* GHC.Types.[] */));
            break;
          case 9:
            return B(_1M/* GHC.Show.$wshowSignedInt */(0, E(_CO/* s8tn */.b), _k/* GHC.Types.[] */));
            break;
          case 10:
            return B(_1M/* GHC.Show.$wshowSignedInt */(0, E(_CO/* s8tn */.b), _k/* GHC.Types.[] */));
            break;
          default:
            return E(_vn/* FormEngine.FormElement.Rendering.lvl48 */);
        }
      },1), E(_CM/* s8ti */), _/* EXTERNAL */)),
      _CP/* s8tM */ = B(_sb/* FormEngine.JQuery.$wa30 */(function(_CQ/* s8tJ */, _/* EXTERNAL */){
        return new F(function(){return _t7/* FormEngine.FormElement.Rendering.a4 */(_ww/* s87w */, _/* EXTERNAL */);});
      }, E(_CN/* s8tE */), _/* EXTERNAL */)),
      _CR/* s8tU */ = B(_sr/* FormEngine.JQuery.$wa31 */(function(_CS/* s8tR */, _/* EXTERNAL */){
        return new F(function(){return _sS/* FormEngine.FormElement.Rendering.a3 */(_ww/* s87w */, _/* EXTERNAL */);});
      }, E(_CP/* s8tM */), _/* EXTERNAL */)),
      _CT/* s8tZ */ = E(_B/* FormEngine.JQuery.addClassInside_f3 */),
      _CU/* s8u2 */ = __app1/* EXTERNAL */(_CT/* s8tZ */, E(_CR/* s8tU */)),
      _CV/* s8u5 */ = E(_A/* FormEngine.JQuery.addClassInside_f2 */),
      _CW/* s8u8 */ = __app1/* EXTERNAL */(_CV/* s8u5 */, _CU/* s8u2 */),
      _CX/* s8ub */ = B(_X/* FormEngine.JQuery.$wa3 */(_v0/* FormEngine.FormElement.Rendering.lvl25 */, _CW/* s8u8 */, _/* EXTERNAL */)),
      _CY/* s8ut */ = B(_C/* FormEngine.JQuery.$wa20 */(_uZ/* FormEngine.FormElement.Rendering.lvl24 */, new T(function(){
        return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_CK/* s8tc */)).b));
      },1), E(_CX/* s8ub */), _/* EXTERNAL */)),
      _CZ/* s8uw */ = function(_/* EXTERNAL */, _D0/* s8uy */){
        var _D1/* s8uz */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_uX/* FormEngine.FormElement.Rendering.lvl22 */, new T(function(){
            return B(_um/* FormEngine.FormElement.Identifiers.checkboxId */(_ww/* s87w */));
          },1)));
        }),
        _D2/* s8v6 */ = B(_rV/* FormEngine.JQuery.$wa23 */(function(_D3/* s8uB */, _/* EXTERNAL */){
          var _D4/* s8uD */ = B(_2E/* FormEngine.JQuery.select1 */(_D1/* s8uz */, _/* EXTERNAL */)),
          _D5/* s8uL */ = __app1/* EXTERNAL */(E(_wo/* FormEngine.JQuery.target_f1 */), E(_D3/* s8uB */)),
          _D6/* s8uR */ = __app1/* EXTERNAL */(E(_uy/* FormEngine.JQuery.isChecked_f1 */), _D5/* s8uL */);
          if(!_D6/* s8uR */){
            var _D7/* s8uX */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2X/* FormEngine.JQuery.disappearJq2 */, E(_D4/* s8uD */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }else{
            var _D8/* s8v2 */ = B(_K/* FormEngine.JQuery.$wa2 */(_2m/* FormEngine.JQuery.appearJq3 */, _2l/* FormEngine.JQuery.appearJq2 */, E(_D4/* s8uD */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }
        }, _D0/* s8uy */, _/* EXTERNAL */)),
        _D9/* s8v9 */ = B(_sJ/* FormEngine.FormElement.Rendering.a2 */(_ww/* s87w */, _D2/* s8v6 */, _/* EXTERNAL */)),
        _Da/* s8vc */ = function(_/* EXTERNAL */, _Db/* s8ve */){
          var _Dc/* s8vr */ = function(_/* EXTERNAL */, _Dd/* s8vt */){
            var _De/* s8vu */ = E(_CL/* s8te */);
            if(!_De/* s8vu */._){
              return new F(function(){return __app1/* EXTERNAL */(E(_z/* FormEngine.JQuery.addClassInside_f1 */), _Dd/* s8vt */);});
            }else{
              var _Df/* s8vE */ = B(_X/* FormEngine.JQuery.$wa3 */(_uV/* FormEngine.FormElement.Rendering.lvl20 */, _Dd/* s8vt */, _/* EXTERNAL */)),
              _Dg/* s8vK */ = B(_C/* FormEngine.JQuery.$wa20 */(_ti/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                return B(_um/* FormEngine.FormElement.Identifiers.checkboxId */(_ww/* s87w */));
              },1), E(_Df/* s8vE */), _/* EXTERNAL */)),
              _Dh/* s8vQ */ = __app1/* EXTERNAL */(_CT/* s8tZ */, E(_Dg/* s8vK */)),
              _Di/* s8vU */ = __app1/* EXTERNAL */(_CV/* s8u5 */, _Dh/* s8vQ */),
              _Dj/* s8vY */ = function(_Dk/* s8w6 */, _Dl/* s8w7 */, _/* EXTERNAL */){
                while(1){
                  var _Dm/* s8w9 */ = E(_Dk/* s8w6 */);
                  if(!_Dm/* s8w9 */._){
                    return _Dl/* s8w7 */;
                  }else{
                    var _Dn/* s8wc */ = B(_wp/* FormEngine.FormElement.Rendering.foldElements2 */(_Dm/* s8w9 */.a, _wr/* s87p */, _ws/* s87q */, _Dl/* s8w7 */, _/* EXTERNAL */));
                    _Dk/* s8w6 */ = _Dm/* s8w9 */.b;
                    _Dl/* s8w7 */ = _Dn/* s8wc */;
                    continue;
                  }
                }
              },
              _Do/* s8wg */ = B((function(_Dp/* s8vZ */, _Dq/* s8w0 */, _Dr/* s8w1 */, _/* EXTERNAL */){
                var _Ds/* s8w3 */ = B(_wp/* FormEngine.FormElement.Rendering.foldElements2 */(_Dp/* s8vZ */, _wr/* s87p */, _ws/* s87q */, _Dr/* s8w1 */, _/* EXTERNAL */));
                return new F(function(){return _Dj/* s8vY */(_Dq/* s8w0 */, _Ds/* s8w3 */, _/* EXTERNAL */);});
              })(_De/* s8vu */.a, _De/* s8vu */.b, _Di/* s8vU */, _/* EXTERNAL */)),
              _Dt/* s8wl */ = E(_z/* FormEngine.JQuery.addClassInside_f1 */),
              _Du/* s8wo */ = __app1/* EXTERNAL */(_Dt/* s8wl */, E(_Do/* s8wg */));
              return new F(function(){return __app1/* EXTERNAL */(_Dt/* s8wl */, _Du/* s8wo */);});
            }
          },
          _Dv/* s8ww */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_CK/* s8tc */)).e);
          if(!_Dv/* s8ww */._){
            return new F(function(){return _Dc/* s8vr */(_/* EXTERNAL */, _Db/* s8ve */);});
          }else{
            var _Dw/* s8wy */ = B(_X/* FormEngine.JQuery.$wa3 */(_sx/* FormEngine.FormElement.Rendering.lvl */, _Db/* s8ve */, _/* EXTERNAL */)),
            _Dx/* s8wD */ = B(_12/* FormEngine.JQuery.$wa34 */(_Dv/* s8ww */.a, E(_Dw/* s8wy */), _/* EXTERNAL */));
            return new F(function(){return _Dc/* s8vr */(_/* EXTERNAL */, E(_Dx/* s8wD */));});
          }
        };
        if(!E(_CL/* s8te */)._){
          var _Dy/* s8wL */ = B(_X/* FormEngine.JQuery.$wa3 */(_k/* GHC.Types.[] */, E(_D9/* s8v9 */), _/* EXTERNAL */));
          return new F(function(){return _Da/* s8vc */(_/* EXTERNAL */, E(_Dy/* s8wL */));});
        }else{
          var _Dz/* s8wU */ = B(_X/* FormEngine.JQuery.$wa3 */(_uW/* FormEngine.FormElement.Rendering.lvl21 */, E(_D9/* s8v9 */), _/* EXTERNAL */));
          return new F(function(){return _Da/* s8vc */(_/* EXTERNAL */, E(_Dz/* s8wU */));});
        }
      };
      if(!E(_ww/* s87w */.b)){
        return new F(function(){return _CZ/* s8uw */(_/* EXTERNAL */, E(_CY/* s8ut */));});
      }else{
        var _DA/* s8x4 */ = B(_C/* FormEngine.JQuery.$wa20 */(_uY/* FormEngine.FormElement.Rendering.lvl23 */, _uY/* FormEngine.FormElement.Rendering.lvl23 */, E(_CY/* s8ut */), _/* EXTERNAL */));
        return new F(function(){return _CZ/* s8uw */(_/* EXTERNAL */, E(_DA/* s8x4 */));});
      }
      break;
    case 10:
      return new F(function(){return _uo/* FormEngine.JQuery.errorjq1 */(_uU/* FormEngine.FormElement.Rendering.lvl19 */, _wt/* s87r */, _/* EXTERNAL */);});
      break;
    case 11:
      var _DB/* s8xg */ = B(_X/* FormEngine.JQuery.$wa3 */(_uR/* FormEngine.FormElement.Rendering.lvl16 */, E(_wt/* s87r */), _/* EXTERNAL */)),
      _DC/* s8xl */ = E(_B/* FormEngine.JQuery.addClassInside_f3 */),
      _DD/* s8xo */ = __app1/* EXTERNAL */(_DC/* s8xl */, E(_DB/* s8xg */)),
      _DE/* s8xr */ = E(_A/* FormEngine.JQuery.addClassInside_f2 */),
      _DF/* s8xu */ = __app1/* EXTERNAL */(_DE/* s8xr */, _DD/* s8xo */),
      _DG/* s8xx */ = B(_X/* FormEngine.JQuery.$wa3 */(_tk/* FormEngine.FormElement.Rendering.lvl6 */, _DF/* s8xu */, _/* EXTERNAL */)),
      _DH/* s8xD */ = __app1/* EXTERNAL */(_DC/* s8xl */, E(_DG/* s8xx */)),
      _DI/* s8xH */ = __app1/* EXTERNAL */(_DE/* s8xr */, _DH/* s8xD */),
      _DJ/* s8xK */ = B(_X/* FormEngine.JQuery.$wa3 */(_tl/* FormEngine.FormElement.Rendering.lvl7 */, _DI/* s8xH */, _/* EXTERNAL */)),
      _DK/* s8xQ */ = __app1/* EXTERNAL */(_DC/* s8xl */, E(_DJ/* s8xK */)),
      _DL/* s8xU */ = __app1/* EXTERNAL */(_DE/* s8xr */, _DK/* s8xQ */),
      _DM/* s8xX */ = B(_X/* FormEngine.JQuery.$wa3 */(_uQ/* FormEngine.FormElement.Rendering.lvl15 */, _DL/* s8xU */, _/* EXTERNAL */)),
      _DN/* s8y3 */ = __app1/* EXTERNAL */(_DC/* s8xl */, E(_DM/* s8xX */)),
      _DO/* s8y7 */ = __app1/* EXTERNAL */(_DE/* s8xr */, _DN/* s8y3 */),
      _DP/* s8ya */ = B(_X/* FormEngine.JQuery.$wa3 */(_uT/* FormEngine.FormElement.Rendering.lvl18 */, _DO/* s8y7 */, _/* EXTERNAL */)),
      _DQ/* s8yu */ = B(_C/* FormEngine.JQuery.$wa20 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, new T(function(){
        var _DR/* s8yr */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ww/* s87w */.a)).a);
        if(!_DR/* s8yr */._){
          return E(_uS/* FormEngine.FormElement.Rendering.lvl17 */);
        }else{
          return E(_DR/* s8yr */.a);
        }
      },1), E(_DP/* s8ya */), _/* EXTERNAL */)),
      _DS/* s8yz */ = E(_z/* FormEngine.JQuery.addClassInside_f1 */),
      _DT/* s8yC */ = __app1/* EXTERNAL */(_DS/* s8yz */, E(_DQ/* s8yu */)),
      _DU/* s8yG */ = __app1/* EXTERNAL */(_DS/* s8yz */, _DT/* s8yC */),
      _DV/* s8yK */ = __app1/* EXTERNAL */(_DS/* s8yz */, _DU/* s8yG */),
      _DW/* s8yO */ = __app1/* EXTERNAL */(_DS/* s8yz */, _DV/* s8yK */);
      return new F(function(){return _sB/* FormEngine.FormElement.Rendering.a1 */(_ww/* s87w */, _DW/* s8yO */, _/* EXTERNAL */);});
      break;
    default:
      var _DX/* s8yW */ = B(_X/* FormEngine.JQuery.$wa3 */(_uR/* FormEngine.FormElement.Rendering.lvl16 */, E(_wt/* s87r */), _/* EXTERNAL */)),
      _DY/* s8z1 */ = E(_B/* FormEngine.JQuery.addClassInside_f3 */),
      _DZ/* s8z4 */ = __app1/* EXTERNAL */(_DY/* s8z1 */, E(_DX/* s8yW */)),
      _E0/* s8z7 */ = E(_A/* FormEngine.JQuery.addClassInside_f2 */),
      _E1/* s8za */ = __app1/* EXTERNAL */(_E0/* s8z7 */, _DZ/* s8z4 */),
      _E2/* s8zd */ = B(_X/* FormEngine.JQuery.$wa3 */(_tk/* FormEngine.FormElement.Rendering.lvl6 */, _E1/* s8za */, _/* EXTERNAL */)),
      _E3/* s8zj */ = __app1/* EXTERNAL */(_DY/* s8z1 */, E(_E2/* s8zd */)),
      _E4/* s8zn */ = __app1/* EXTERNAL */(_E0/* s8z7 */, _E3/* s8zj */),
      _E5/* s8zq */ = B(_X/* FormEngine.JQuery.$wa3 */(_tl/* FormEngine.FormElement.Rendering.lvl7 */, _E4/* s8zn */, _/* EXTERNAL */)),
      _E6/* s8zw */ = __app1/* EXTERNAL */(_DY/* s8z1 */, E(_E5/* s8zq */)),
      _E7/* s8zA */ = __app1/* EXTERNAL */(_E0/* s8z7 */, _E6/* s8zw */),
      _E8/* s8zD */ = B(_X/* FormEngine.JQuery.$wa3 */(_uQ/* FormEngine.FormElement.Rendering.lvl15 */, _E7/* s8zA */, _/* EXTERNAL */)),
      _E9/* s8zJ */ = __app1/* EXTERNAL */(_DY/* s8z1 */, E(_E8/* s8zD */)),
      _Ea/* s8zN */ = __app1/* EXTERNAL */(_E0/* s8z7 */, _E9/* s8zJ */),
      _Eb/* s8zQ */ = B(_X/* FormEngine.JQuery.$wa3 */(_uP/* FormEngine.FormElement.Rendering.lvl14 */, _Ea/* s8zN */, _/* EXTERNAL */)),
      _Ec/* s8Aa */ = B(_C/* FormEngine.JQuery.$wa20 */(_uO/* FormEngine.FormElement.Rendering.lvl13 */, new T(function(){
        var _Ed/* s8A7 */ = E(B(_1A/* FormEngine.FormItem.fiDescriptor */(_ww/* s87w */.a)).a);
        if(!_Ed/* s8A7 */._){
          return E(_uN/* FormEngine.FormElement.Rendering.lvl12 */);
        }else{
          return E(_Ed/* s8A7 */.a);
        }
      },1), E(_Eb/* s8zQ */), _/* EXTERNAL */)),
      _Ee/* s8Af */ = E(_z/* FormEngine.JQuery.addClassInside_f1 */),
      _Ef/* s8Ai */ = __app1/* EXTERNAL */(_Ee/* s8Af */, E(_Ec/* s8Aa */)),
      _Eg/* s8Am */ = __app1/* EXTERNAL */(_Ee/* s8Af */, _Ef/* s8Ai */),
      _Eh/* s8Aq */ = __app1/* EXTERNAL */(_Ee/* s8Af */, _Eg/* s8Am */),
      _Ei/* s8Au */ = __app1/* EXTERNAL */(_Ee/* s8Af */, _Eh/* s8Aq */);
      return new F(function(){return _sB/* FormEngine.FormElement.Rendering.a1 */(_ww/* s87w */, _Ei/* s8Au */, _/* EXTERNAL */);});
  }
},
_Ej/* foldElements1 */ = function(_Ek/* s8Ay */, _El/* s8Az */, _Em/* s8AA */, _En/* s8AB */, _/* EXTERNAL */){
  var _Eo/* s8AD */ = function(_Ep/* s8AE */, _Eq/* s8AF */, _/* EXTERNAL */){
    while(1){
      var _Er/* s8AH */ = E(_Ep/* s8AE */);
      if(!_Er/* s8AH */._){
        return _Eq/* s8AF */;
      }else{
        var _Es/* s8AK */ = B(_wp/* FormEngine.FormElement.Rendering.foldElements2 */(_Er/* s8AH */.a, _El/* s8Az */, _Em/* s8AA */, _Eq/* s8AF */, _/* EXTERNAL */));
        _Ep/* s8AE */ = _Er/* s8AH */.b;
        _Eq/* s8AF */ = _Es/* s8AK */;
        continue;
      }
    }
  };
  return new F(function(){return _Eo/* s8AD */(_Ek/* s8Ay */, _En/* s8AB */, _/* EXTERNAL */);});
},
_Et/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("img/invalid.png\'/>"));
}),
_Eu/* baseURL */ = new T(function(){
  return B(unCStr/* EXTERNAL */("/"));
}),
_Ev/* staticURL1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("static/"));
}),
_Ew/* staticURL */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_Eu/* Config.Config.baseURL */, _Ev/* Config.Config.staticURL1 */));
}),
_Ex/* lvl11 */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_Ew/* Config.Config.staticURL */, _Et/* Form.lvl10 */));
}),
_Ey/* lvl12 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img alt=\'invalid\' class=\'validity-flag\' src=\'", _Ex/* Form.lvl11 */));
}),
_Ez/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("img/question.png\'/>"));
}),
_EA/* lvl14 */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_Ew/* Config.Config.staticURL */, _Ez/* Form.lvl13 */));
}),
_EB/* lvl15 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img alt=\'details\' src=\'", _EA/* Form.lvl14 */));
}),
_EC/* Just */ = function(_ED/* B1 */){
  return new T1(1,_ED/* B1 */);
},
_EE/* $fJSTypeJSString */ = new T2(0,_bM/* GHC.Base.id */,_EC/* GHC.Base.Just */),
_EF/* fromJSStr */ = function(_EG/* sdrS */){
  return new F(function(){return fromJSStr/* EXTERNAL */(E(_EG/* sdrS */));});
},
_EH/* $fJSType[]_$cfromJSString */ = function(_EI/* s3BE */){
  return new T1(1,new T(function(){
    return B(_EF/* GHC.HastePrim.fromJSStr */(_EI/* s3BE */));
  }));
},
_EJ/* toJSStr1 */ = function(_EK/* sdrX */){
  return new F(function(){return toJSStr/* EXTERNAL */(E(_EK/* sdrX */));});
},
_EL/* $fJSType[] */ = new T2(0,_EJ/* GHC.HastePrim.toJSStr1 */,_EH/* Haste.Prim.JSType.$fJSType[]_$cfromJSString */),
_EM/* $fApplicativeIO1 */ = function(_EN/* s3hg */, _EO/* s3hh */, _/* EXTERNAL */){
  var _EP/* s3hj */ = B(A1(_EN/* s3hg */,_/* EXTERNAL */)),
  _EQ/* s3hm */ = B(A1(_EO/* s3hh */,_/* EXTERNAL */));
  return _EP/* s3hj */;
},
_ER/* $fApplicativeIO2 */ = function(_ES/* s3gu */, _ET/* s3gv */, _/* EXTERNAL */){
  var _EU/* s3gx */ = B(A1(_ES/* s3gu */,_/* EXTERNAL */)),
  _EV/* s3gA */ = B(A1(_ET/* s3gv */,_/* EXTERNAL */));
  return new T(function(){
    return B(A1(_EU/* s3gx */,_EV/* s3gA */));
  });
},
_EW/* $fFunctorIO1 */ = function(_EX/* s3gZ */, _EY/* s3h0 */, _/* EXTERNAL */){
  var _EZ/* s3h2 */ = B(A1(_EY/* s3h0 */,_/* EXTERNAL */));
  return _EX/* s3gZ */;
},
_F0/* $fFunctorIO2 */ = function(_F1/* s3gS */, _F2/* s3gT */, _/* EXTERNAL */){
  var _F3/* s3gV */ = B(A1(_F2/* s3gT */,_/* EXTERNAL */));
  return new T(function(){
    return B(A1(_F1/* s3gS */,_F3/* s3gV */));
  });
},
_F4/* $fFunctorIO */ = new T2(0,_F0/* GHC.Base.$fFunctorIO2 */,_EW/* GHC.Base.$fFunctorIO1 */),
_F5/* returnIO1 */ = function(_F6/* s3g7 */, _/* EXTERNAL */){
  return _F6/* s3g7 */;
},
_F7/* thenIO1 */ = function(_F8/* s3g1 */, _F9/* s3g2 */, _/* EXTERNAL */){
  var _Fa/* s3g4 */ = B(A1(_F8/* s3g1 */,_/* EXTERNAL */));
  return new F(function(){return A1(_F9/* s3g2 */,_/* EXTERNAL */);});
},
_Fb/* $fApplicativeIO */ = new T5(0,_F4/* GHC.Base.$fFunctorIO */,_F5/* GHC.Base.returnIO1 */,_ER/* GHC.Base.$fApplicativeIO2 */,_F7/* GHC.Base.thenIO1 */,_EM/* GHC.Base.$fApplicativeIO1 */),
_Fc/* $fExceptionAllocationLimitExceeded_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_Fd/* $fExceptionAllocationLimitExceeded_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GHC.IO.Exception"));
}),
_Fe/* $fExceptionIOException_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IOException"));
}),
_Ff/* $fExceptionIOException_wild */ = new T5(0,new Long/* EXTERNAL */(4053623282, 1685460941, true),new Long/* EXTERNAL */(3693590983, 2507416641, true),_Fc/* GHC.IO.Exception.$fExceptionAllocationLimitExceeded_ww2 */,_Fd/* GHC.IO.Exception.$fExceptionAllocationLimitExceeded_ww4 */,_Fe/* GHC.IO.Exception.$fExceptionIOException_ww4 */),
_Fg/* $fExceptionIOException4 */ = new T5(0,new Long/* EXTERNAL */(4053623282, 1685460941, true),new Long/* EXTERNAL */(3693590983, 2507416641, true),_Ff/* GHC.IO.Exception.$fExceptionIOException_wild */,_k/* GHC.Types.[] */,_k/* GHC.Types.[] */),
_Fh/* $fExceptionIOException3 */ = function(_Fi/* s3K6Q */){
  return E(_Fg/* GHC.IO.Exception.$fExceptionIOException4 */);
},
_Fj/* $fExceptionIOException_$cfromException */ = function(_Fk/* s3KaB */){
  var _Fl/* s3KaC */ = E(_Fk/* s3KaB */);
  return new F(function(){return _8U/* Data.Typeable.cast */(B(_8S/* GHC.Exception.$p1Exception */(_Fl/* s3KaC */.a)), _Fh/* GHC.IO.Exception.$fExceptionIOException3 */, _Fl/* s3KaC */.b);});
},
_Fm/* $fExceptionArrayException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": "));
}),
_Fn/* $fExceptionIOException1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_Fo/* $fExceptionIOException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" ("));
}),
_Fp/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("interrupted"));
}),
_Fq/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("system error"));
}),
_Fr/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("unsatisified constraints"));
}),
_Fs/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("user error"));
}),
_Ft/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("permission denied"));
}),
_Fu/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("illegal operation"));
}),
_Fv/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("end of file"));
}),
_Fw/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource exhausted"));
}),
_Fx/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource busy"));
}),
_Fy/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("does not exist"));
}),
_Fz/* lvl19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("already exists"));
}),
_FA/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource vanished"));
}),
_FB/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("timeout"));
}),
_FC/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("unsupported operation"));
}),
_FD/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("hardware fault"));
}),
_FE/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("inappropriate type"));
}),
_FF/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("invalid argument"));
}),
_FG/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("failed"));
}),
_FH/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("protocol error"));
}),
_FI/* $w$cshowsPrec3 */ = function(_FJ/* s3Kcg */, _FK/* s3Kch */){
  switch(E(_FJ/* s3Kcg */)){
    case 0:
      return new F(function(){return _7/* GHC.Base.++ */(_Fz/* GHC.IO.Exception.lvl19 */, _FK/* s3Kch */);});
      break;
    case 1:
      return new F(function(){return _7/* GHC.Base.++ */(_Fy/* GHC.IO.Exception.lvl18 */, _FK/* s3Kch */);});
      break;
    case 2:
      return new F(function(){return _7/* GHC.Base.++ */(_Fx/* GHC.IO.Exception.lvl17 */, _FK/* s3Kch */);});
      break;
    case 3:
      return new F(function(){return _7/* GHC.Base.++ */(_Fw/* GHC.IO.Exception.lvl16 */, _FK/* s3Kch */);});
      break;
    case 4:
      return new F(function(){return _7/* GHC.Base.++ */(_Fv/* GHC.IO.Exception.lvl15 */, _FK/* s3Kch */);});
      break;
    case 5:
      return new F(function(){return _7/* GHC.Base.++ */(_Fu/* GHC.IO.Exception.lvl14 */, _FK/* s3Kch */);});
      break;
    case 6:
      return new F(function(){return _7/* GHC.Base.++ */(_Ft/* GHC.IO.Exception.lvl13 */, _FK/* s3Kch */);});
      break;
    case 7:
      return new F(function(){return _7/* GHC.Base.++ */(_Fs/* GHC.IO.Exception.lvl12 */, _FK/* s3Kch */);});
      break;
    case 8:
      return new F(function(){return _7/* GHC.Base.++ */(_Fr/* GHC.IO.Exception.lvl11 */, _FK/* s3Kch */);});
      break;
    case 9:
      return new F(function(){return _7/* GHC.Base.++ */(_Fq/* GHC.IO.Exception.lvl10 */, _FK/* s3Kch */);});
      break;
    case 10:
      return new F(function(){return _7/* GHC.Base.++ */(_FH/* GHC.IO.Exception.lvl9 */, _FK/* s3Kch */);});
      break;
    case 11:
      return new F(function(){return _7/* GHC.Base.++ */(_FG/* GHC.IO.Exception.lvl8 */, _FK/* s3Kch */);});
      break;
    case 12:
      return new F(function(){return _7/* GHC.Base.++ */(_FF/* GHC.IO.Exception.lvl7 */, _FK/* s3Kch */);});
      break;
    case 13:
      return new F(function(){return _7/* GHC.Base.++ */(_FE/* GHC.IO.Exception.lvl6 */, _FK/* s3Kch */);});
      break;
    case 14:
      return new F(function(){return _7/* GHC.Base.++ */(_FD/* GHC.IO.Exception.lvl5 */, _FK/* s3Kch */);});
      break;
    case 15:
      return new F(function(){return _7/* GHC.Base.++ */(_FC/* GHC.IO.Exception.lvl4 */, _FK/* s3Kch */);});
      break;
    case 16:
      return new F(function(){return _7/* GHC.Base.++ */(_FB/* GHC.IO.Exception.lvl3 */, _FK/* s3Kch */);});
      break;
    case 17:
      return new F(function(){return _7/* GHC.Base.++ */(_FA/* GHC.IO.Exception.lvl2 */, _FK/* s3Kch */);});
      break;
    default:
      return new F(function(){return _7/* GHC.Base.++ */(_Fp/* GHC.IO.Exception.lvl1 */, _FK/* s3Kch */);});
  }
},
_FL/* showHandle1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}"));
}),
_FM/* showHandle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("{handle: "));
}),
_FN/* $w$cshowsPrec2 */ = function(_FO/* s3Kcp */, _FP/* s3Kcq */, _FQ/* s3Kcr */, _FR/* s3Kcs */, _FS/* s3Kct */, _FT/* s3Kcu */){
  var _FU/* s3Kcv */ = new T(function(){
    var _FV/* s3Kcw */ = new T(function(){
      var _FW/* s3KcC */ = new T(function(){
        var _FX/* s3Kcx */ = E(_FR/* s3Kcs */);
        if(!_FX/* s3Kcx */._){
          return E(_FT/* s3Kcu */);
        }else{
          var _FY/* s3KcB */ = new T(function(){
            return B(_7/* GHC.Base.++ */(_FX/* s3Kcx */, new T(function(){
              return B(_7/* GHC.Base.++ */(_Fn/* GHC.IO.Exception.$fExceptionIOException1 */, _FT/* s3Kcu */));
            },1)));
          },1);
          return B(_7/* GHC.Base.++ */(_Fo/* GHC.IO.Exception.$fExceptionIOException2 */, _FY/* s3KcB */));
        }
      },1);
      return B(_FI/* GHC.IO.Exception.$w$cshowsPrec3 */(_FP/* s3Kcq */, _FW/* s3KcC */));
    }),
    _FZ/* s3KcD */ = E(_FQ/* s3Kcr */);
    if(!_FZ/* s3KcD */._){
      return E(_FV/* s3Kcw */);
    }else{
      return B(_7/* GHC.Base.++ */(_FZ/* s3KcD */, new T(function(){
        return B(_7/* GHC.Base.++ */(_Fm/* GHC.IO.Exception.$fExceptionArrayException2 */, _FV/* s3Kcw */));
      },1)));
    }
  }),
  _G0/* s3KcH */ = E(_FS/* s3Kct */);
  if(!_G0/* s3KcH */._){
    var _G1/* s3KcI */ = E(_FO/* s3Kcp */);
    if(!_G1/* s3KcI */._){
      return E(_FU/* s3Kcv */);
    }else{
      var _G2/* s3KcK */ = E(_G1/* s3KcI */.a);
      if(!_G2/* s3KcK */._){
        var _G3/* s3KcP */ = new T(function(){
          var _G4/* s3KcO */ = new T(function(){
            return B(_7/* GHC.Base.++ */(_FL/* GHC.IO.Handle.Types.showHandle1 */, new T(function(){
              return B(_7/* GHC.Base.++ */(_Fm/* GHC.IO.Exception.$fExceptionArrayException2 */, _FU/* s3Kcv */));
            },1)));
          },1);
          return B(_7/* GHC.Base.++ */(_G2/* s3KcK */.a, _G4/* s3KcO */));
        },1);
        return new F(function(){return _7/* GHC.Base.++ */(_FM/* GHC.IO.Handle.Types.showHandle2 */, _G3/* s3KcP */);});
      }else{
        var _G5/* s3KcV */ = new T(function(){
          var _G6/* s3KcU */ = new T(function(){
            return B(_7/* GHC.Base.++ */(_FL/* GHC.IO.Handle.Types.showHandle1 */, new T(function(){
              return B(_7/* GHC.Base.++ */(_Fm/* GHC.IO.Exception.$fExceptionArrayException2 */, _FU/* s3Kcv */));
            },1)));
          },1);
          return B(_7/* GHC.Base.++ */(_G2/* s3KcK */.a, _G6/* s3KcU */));
        },1);
        return new F(function(){return _7/* GHC.Base.++ */(_FM/* GHC.IO.Handle.Types.showHandle2 */, _G5/* s3KcV */);});
      }
    }
  }else{
    return new F(function(){return _7/* GHC.Base.++ */(_G0/* s3KcH */.a, new T(function(){
      return B(_7/* GHC.Base.++ */(_Fm/* GHC.IO.Exception.$fExceptionArrayException2 */, _FU/* s3Kcv */));
    },1));});
  }
},
_G7/* $fExceptionIOException_$cshow */ = function(_G8/* s3Kd8 */){
  var _G9/* s3Kd9 */ = E(_G8/* s3Kd8 */);
  return new F(function(){return _FN/* GHC.IO.Exception.$w$cshowsPrec2 */(_G9/* s3Kd9 */.a, _G9/* s3Kd9 */.b, _G9/* s3Kd9 */.c, _G9/* s3Kd9 */.d, _G9/* s3Kd9 */.f, _k/* GHC.Types.[] */);});
},
_Ga/* $fExceptionIOException_$ctoException */ = function(_Gb/* B1 */){
  return new T2(0,_Gc/* GHC.IO.Exception.$fExceptionIOException */,_Gb/* B1 */);
},
_Gd/* $fExceptionIOException_$cshowsPrec */ = function(_Ge/* s3KcY */, _Gf/* s3KcZ */, _Gg/* s3Kd0 */){
  var _Gh/* s3Kd1 */ = E(_Gf/* s3KcZ */);
  return new F(function(){return _FN/* GHC.IO.Exception.$w$cshowsPrec2 */(_Gh/* s3Kd1 */.a, _Gh/* s3Kd1 */.b, _Gh/* s3Kd1 */.c, _Gh/* s3Kd1 */.d, _Gh/* s3Kd1 */.f, _Gg/* s3Kd0 */);});
},
_Gi/* $s$dmshow9 */ = function(_Gj/* s3Kdg */, _Gk/* s3Kdh */){
  var _Gl/* s3Kdi */ = E(_Gj/* s3Kdg */);
  return new F(function(){return _FN/* GHC.IO.Exception.$w$cshowsPrec2 */(_Gl/* s3Kdi */.a, _Gl/* s3Kdi */.b, _Gl/* s3Kdi */.c, _Gl/* s3Kdi */.d, _Gl/* s3Kdi */.f, _Gk/* s3Kdh */);});
},
_Gm/* $fShowIOException_$cshowList */ = function(_Gn/* s3Kdp */, _Go/* s3Kdq */){
  return new F(function(){return _5t/* GHC.Show.showList__ */(_Gi/* GHC.IO.Exception.$s$dmshow9 */, _Gn/* s3Kdp */, _Go/* s3Kdq */);});
},
_Gp/* $fShowIOException */ = new T3(0,_Gd/* GHC.IO.Exception.$fExceptionIOException_$cshowsPrec */,_G7/* GHC.IO.Exception.$fExceptionIOException_$cshow */,_Gm/* GHC.IO.Exception.$fShowIOException_$cshowList */),
_Gc/* $fExceptionIOException */ = new T(function(){
  return new T5(0,_Fh/* GHC.IO.Exception.$fExceptionIOException3 */,_Gp/* GHC.IO.Exception.$fShowIOException */,_Ga/* GHC.IO.Exception.$fExceptionIOException_$ctoException */,_Fj/* GHC.IO.Exception.$fExceptionIOException_$cfromException */,_G7/* GHC.IO.Exception.$fExceptionIOException_$cshow */);
}),
_Gq/* $fxExceptionIOException */ = new T(function(){
  return E(_Gc/* GHC.IO.Exception.$fExceptionIOException */);
}),
_Gr/* UserError */ = 7,
_Gs/* userError */ = function(_Gt/* s3K6P */){
  return new T6(0,_4y/* GHC.Base.Nothing */,_Gr/* GHC.IO.Exception.UserError */,_k/* GHC.Types.[] */,_Gt/* s3K6P */,_4y/* GHC.Base.Nothing */,_4y/* GHC.Base.Nothing */);
},
_Gu/* failIO1 */ = function(_Gv/* s2WaY */, _/* EXTERNAL */){
  var _Gw/* s2Wb1 */ = new T(function(){
    return B(A2(_9m/* GHC.Exception.toException */,_Gq/* GHC.IO.Exception.$fxExceptionIOException */, new T(function(){
      return B(A1(_Gs/* GHC.IO.Exception.userError */,_Gv/* s2WaY */));
    })));
  });
  return new F(function(){return die/* EXTERNAL */(_Gw/* s2Wb1 */);});
},
_Gx/* failIO */ = function(_Gy/* B2 */, _/* EXTERNAL */){
  return new F(function(){return _Gu/* GHC.IO.failIO1 */(_Gy/* B2 */, _/* EXTERNAL */);});
},
_Gz/* $fMonadIO_$cfail */ = function(_GA/* s3ek */){
  return new F(function(){return A1(_Gx/* GHC.IO.failIO */,_GA/* s3ek */);});
},
_GB/* bindIO1 */ = function(_GC/* s3g9 */, _GD/* s3ga */, _/* EXTERNAL */){
  var _GE/* s3gc */ = B(A1(_GC/* s3g9 */,_/* EXTERNAL */));
  return new F(function(){return A2(_GD/* s3ga */,_GE/* s3gc */, _/* EXTERNAL */);});
},
_GF/* $fMonadIO */ = new T5(0,_Fb/* GHC.Base.$fApplicativeIO */,_GB/* GHC.Base.bindIO1 */,_F7/* GHC.Base.thenIO1 */,_F5/* GHC.Base.returnIO1 */,_Gz/* GHC.Base.$fMonadIO_$cfail */),
_GG/* $fMonadIOIO */ = new T2(0,_GF/* GHC.Base.$fMonadIO */,_bM/* GHC.Base.id */),
_GH/* POST */ = 1,
_GI/* $fToAnyMethod1 */ = "POST",
_GJ/* $fToAnyMethod2 */ = "GET",
_GK/* lvl2 */ = "=",
_GL/* lvl3 */ = "&",
_GM/* toJSString */ = function(_GN/* s3zz */){
  return E(E(_GN/* s3zz */).a);
},
_GO/* $wtoQueryString */ = function(_GP/* sd4I */, _GQ/* sd4J */, _GR/* sd4K */){
  var _GS/* sd50 */ = function(_GT/* sd4L */){
    var _GU/* sd4M */ = E(_GT/* sd4L */);
    return new F(function(){return jsCat/* EXTERNAL */(new T2(1,new T(function(){
      return B(A2(_GM/* Haste.Prim.JSType.toJSString */,_GP/* sd4I */, _GU/* sd4M */.a));
    }),new T2(1,new T(function(){
      return B(A2(_GM/* Haste.Prim.JSType.toJSString */,_GQ/* sd4J */, _GU/* sd4M */.b));
    }),_k/* GHC.Types.[] */)), E(_GK/* Haste.Ajax.lvl2 */));});
  },
  _GV/* sd56 */ = jsCat/* EXTERNAL */(B(_8H/* GHC.Base.map */(_GS/* sd50 */, _GR/* sd4K */)), E(_GL/* Haste.Ajax.lvl3 */));
  return E(_GV/* sd56 */);
},
_GW/* f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(method, url, async, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, url, async);if(method == \'POST\') {xhr.setRequestHeader(\'Content-type\',\'application/x-www-form-urlencoded\');}xhr.onreadystatechange = function() {if(xhr.readyState == 4) {cb(xhr.status == 200 ? xhr.responseText : null);}};xhr.send(postdata);})");
}),
_GX/* fromJSString */ = function(_GY/* s3zD */){
  return E(E(_GY/* s3zD */).b);
},
_GZ/* liftIO */ = function(_H0/* stz */){
  return E(E(_H0/* stz */).b);
},
_H1/* lvl */ = new T(function(){
  return toJSStr/* EXTERNAL */(_k/* GHC.Types.[] */);
}),
_H2/* lvl1 */ = "?",
_H3/* ajaxRequest */ = function(_H4/* sd5x */, _H5/* sd5y */, _H6/* sd5z */, _H7/* sd5A */, _H8/* sd5B */, _H9/* sd5C */, _Ha/* sd5D */, _Hb/* sd5E */){
  var _Hc/* sd5H */ = new T(function(){
    return B(_GO/* Haste.Ajax.$wtoQueryString */(_H5/* sd5y */, _H6/* sd5z */, _Ha/* sd5D */));
  }),
  _Hd/* sd5F */ = new T(function(){
    return B(_EJ/* GHC.HastePrim.toJSStr1 */(_H9/* sd5C */));
  }),
  _He/* sd70 */ = function(_/* EXTERNAL */){
    var _Hf/* sd5M */ = function(_Hg/* sd5N */){
      var _Hh/* sd5O */ = function(_Hi/* sd5P */){
        var _Hj/* sd5Q */ = function(_Hk/* sd5R */){
          var _Hl/* sd5S */ = new T(function(){
            return B(_GX/* Haste.Prim.JSType.fromJSString */(_H7/* sd5A */));
          }),
          _Hm/* sd6d */ = function(_Hn/* sd5T */, _/* EXTERNAL */){
            var _Ho/* sd69 */ = new T(function(){
              var _Hp/* sd5V */ = E(_Hn/* sd5T */),
              _Hq/* sd60 */ = __eq/* EXTERNAL */(_Hp/* sd5V */, E(_1p/* Haste.Prim.Any.jsNull */));
              if(!E(_Hq/* sd60 */)){
                return B(A1(_Hl/* sd5S */,new T(function(){
                  return String/* EXTERNAL */(_Hp/* sd5V */);
                })));
              }else{
                return __Z/* EXTERNAL */;
              }
            }),
            _Hr/* sd6a */ = B(A2(_Hb/* sd5E */,_Ho/* sd69 */, _/* EXTERNAL */));
            return _1p/* Haste.Prim.Any.jsNull */;
          },
          _Hs/* sd6h */ = __createJSFunc/* EXTERNAL */(2, E(_Hm/* sd6d */)),
          _Ht/* sd6p */ = __app5/* EXTERNAL */(E(_GW/* Haste.Ajax.f1 */), _Hg/* sd5N */, _Hi/* sd5P */, true, _Hk/* sd5R */, _Hs/* sd6h */);
          return _0/* GHC.Tuple.() */;
        };
        if(!E(_H8/* sd5B */)){
          return new F(function(){return _Hj/* sd5Q */(E(_H1/* Haste.Ajax.lvl */));});
        }else{
          var _Hu/* sd6v */ = E(_Ha/* sd5D */);
          if(!_Hu/* sd6v */._){
            return new F(function(){return _Hj/* sd5Q */(E(_H1/* Haste.Ajax.lvl */));});
          }else{
            return new F(function(){return _Hj/* sd5Q */(B(_GO/* Haste.Ajax.$wtoQueryString */(_H5/* sd5y */, _H6/* sd5z */, _Hu/* sd6v */)));});
          }
        }
      };
      if(!E(_H8/* sd5B */)){
        if(!E(_Ha/* sd5D */)._){
          return new F(function(){return _Hh/* sd5O */(toJSStr/* EXTERNAL */(E(_H9/* sd5C */)));});
        }else{
          var _Hv/* sd6N */ = jsCat/* EXTERNAL */(new T2(1,_Hd/* sd5F */,new T2(1,_Hc/* sd5H */,_k/* GHC.Types.[] */)), E(_H2/* Haste.Ajax.lvl1 */));
          return new F(function(){return _Hh/* sd5O */(_Hv/* sd6N */);});
        }
      }else{
        return new F(function(){return _Hh/* sd5O */(toJSStr/* EXTERNAL */(E(_H9/* sd5C */)));});
      }
    };
    if(!E(_H8/* sd5B */)){
      return new F(function(){return _Hf/* sd5M */(E(_GJ/* Haste.Ajax.$fToAnyMethod2 */));});
    }else{
      return new F(function(){return _Hf/* sd5M */(E(_GI/* Haste.Ajax.$fToAnyMethod1 */));});
    }
  };
  return new F(function(){return A2(_GZ/* Control.Monad.IO.Class.liftIO */,_H4/* sd5x */, _He/* sd70 */);});
},
_Hw/* bookAckTxt2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("img/crc-logo.png\' alt=\'CRC logo\'/>      </a>   </p>"));
}),
_Hx/* bookAckTxt1 */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_Ew/* Config.Config.staticURL */, _Hw/* Texts.bookAckTxt2 */));
}),
_Hy/* bookAckTxt */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<hr/>   <p>     (*) With kind permission of     <a href=\'http://taylorandfrancis.com/\' target=\'_blank\'>       <img src=\'", _Hx/* Texts.bookAckTxt1 */));
}),
_Hz/* bookLabelTxt1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": </h1>"));
}),
_HA/* bookLabelTxt2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<h1>   <a href=\'https://www.crcpress.com/Data-Stewardship-for-Discovery-A-Practical-Guide-for-Data-Experts/Mons/p/book/9781498753173\' target=\'_blank\'>Book</a>   (*) chapter "));
}),
_HB/* readEither4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude.read: no parse"));
}),
_HC/* lvl */ = new T(function(){
  return B(err/* EXTERNAL */(_HB/* Text.Read.readEither4 */));
}),
_HD/* readEither2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude.read: ambiguous parse"));
}),
_HE/* lvl1 */ = new T(function(){
  return B(err/* EXTERNAL */(_HD/* Text.Read.readEither2 */));
}),
_HF/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("api/getQuestion"));
}),
_HG/* lvl17 */ = "chid",
_HH/* lvl18 */ = "qid",
_HI/* lvl19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("api/getBookContents"));
}),
_HJ/* $fReadMaybe3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Just"));
}),
_HK/* $fReadMaybe4 */ = 11,
_HL/* $fReadMaybe5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nothing"));
}),
_HM/* readPrec */ = function(_HN/* s1vgA */){
  return E(E(_HN/* s1vgA */).c);
},
_HO/* $fReadMaybe2 */ = function(_HP/* s1vrp */, _HQ/* s1vrq */){
  var _HR/* s1vrr */ = new T(function(){
    return B(_HM/* GHC.Read.readPrec */(_HP/* s1vrp */));
  }),
  _HS/* s1vrZ */ = function(_HT/* s1vrs */, _HU/* s1vrt */){
    var _HV/* s1vru */ = new T(function(){
      var _HW/* s1vrv */ = new T(function(){
        return B(A1(_HU/* s1vrt */,_4y/* GHC.Base.Nothing */));
      });
      return B(_ll/* Text.Read.Lex.expect2 */(function(_HX/* s1vrw */){
        var _HY/* s1vrx */ = E(_HX/* s1vrw */);
        return (_HY/* s1vrx */._==3) ? (!B(_2n/* GHC.Base.eqString */(_HY/* s1vrx */.a, _HL/* GHC.Read.$fReadMaybe5 */))) ? new T0(2) : E(_HW/* s1vrv */) : new T0(2);
      }));
    }),
    _HZ/* s1vrB */ = function(_I0/* s1vrC */){
      return E(_HV/* s1vru */);
    },
    _I1/* s1vrY */ = new T(function(){
      if(E(_HT/* s1vrs */)>10){
        return new T0(2);
      }else{
        var _I2/* s1vrK */ = new T(function(){
          var _I3/* s1vrL */ = new T(function(){
            return B(A2(_HR/* s1vrr */,_HK/* GHC.Read.$fReadMaybe4 */, function(_I4/* s1vrM */){
              return new F(function(){return A1(_HU/* s1vrt */,new T1(1,_I4/* s1vrM */));});
            }));
          });
          return B(_ll/* Text.Read.Lex.expect2 */(function(_I5/* s1vrP */){
            var _I6/* s1vrQ */ = E(_I5/* s1vrP */);
            return (_I6/* s1vrQ */._==3) ? (!B(_2n/* GHC.Base.eqString */(_I6/* s1vrQ */.a, _HJ/* GHC.Read.$fReadMaybe3 */))) ? new T0(2) : E(_I3/* s1vrL */) : new T0(2);
          }));
        }),
        _I7/* s1vrU */ = function(_I8/* s1vrV */){
          return E(_I2/* s1vrK */);
        };
        return new T1(1,function(_I9/* s1vrW */){
          return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_I9/* s1vrW */, _I7/* s1vrU */);});
        });
      }
    });
    return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_Ia/* s1vrD */){
      return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Ia/* s1vrD */, _HZ/* s1vrB */);});
    }), _I1/* s1vrY */);});
  };
  return new F(function(){return _mc/* GHC.Read.$fReadDouble10 */(_HS/* s1vrZ */, _HQ/* s1vrq */);});
},
_Ib/* a2 */ = function(_Ic/* s1vnB */, _Id/* s1vnC */){
  return new F(function(){return _Ie/* GHC.Read.$wa20 */(_Id/* s1vnC */);});
},
_Ie/* $wa20 */ = function(_If/* s1vnD */){
  var _Ig/* s1vnI */ = new T(function(){
    return B(_ll/* Text.Read.Lex.expect2 */(function(_Ih/* s1vnF */){
      var _Ii/* s1vnG */ = E(_Ih/* s1vnF */);
      if(!_Ii/* s1vnG */._){
        return new F(function(){return A1(_If/* s1vnD */,_Ii/* s1vnG */.a);});
      }else{
        return new T0(2);
      }
    }));
  }),
  _Ij/* s1vnJ */ = function(_Ik/* s1vnK */){
    return E(_Ig/* s1vnI */);
  };
  return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_Il/* s1vnL */){
    return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Il/* s1vnL */, _Ij/* s1vnJ */);});
  }), new T(function(){
    return new T1(1,B(_lT/* GHC.Read.$wa3 */(_Ib/* GHC.Read.a2 */, _If/* s1vnD */)));
  }));});
},
_Im/* $fReadChar2 */ = function(_In/* s1vnR */, _Io/* s1vnS */){
  return new F(function(){return _Ie/* GHC.Read.$wa20 */(_Io/* s1vnS */);});
},
_Ip/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("["));
}),
_Iq/* $wa */ = function(_Ir/* s1vjF */, _Is/* s1vjG */){
  var _It/* s1vjH */ = function(_Iu/* s1vjI */, _Iv/* s1vjJ */){
    var _Iw/* s1vjK */ = new T(function(){
      return B(A1(_Iv/* s1vjJ */,_k/* GHC.Types.[] */));
    }),
    _Ix/* s1vjL */ = new T(function(){
      var _Iy/* s1vjQ */ = function(_Iz/* s1vjM */){
        return new F(function(){return _It/* s1vjH */(_8G/* GHC.Types.True */, function(_IA/* s1vjN */){
          return new F(function(){return A1(_Iv/* s1vjJ */,new T2(1,_Iz/* s1vjM */,_IA/* s1vjN */));});
        });});
      };
      return B(A2(_Ir/* s1vjF */,_lS/* Text.ParserCombinators.ReadPrec.minPrec */, _Iy/* s1vjQ */));
    }),
    _IB/* s1vk8 */ = new T(function(){
      return B(_ll/* Text.Read.Lex.expect2 */(function(_IC/* s1vjS */){
        var _ID/* s1vjT */ = E(_IC/* s1vjS */);
        if(_ID/* s1vjT */._==2){
          var _IE/* s1vjV */ = E(_ID/* s1vjT */.a);
          if(!_IE/* s1vjV */._){
            return new T0(2);
          }else{
            var _IF/* s1vjX */ = _IE/* s1vjV */.b;
            switch(E(_IE/* s1vjV */.a)){
              case 44:
                return (E(_IF/* s1vjX */)._==0) ? (!E(_Iu/* s1vjI */)) ? new T0(2) : E(_Ix/* s1vjL */) : new T0(2);
              case 93:
                return (E(_IF/* s1vjX */)._==0) ? E(_Iw/* s1vjK */) : new T0(2);
              default:
                return new T0(2);
            }
          }
        }else{
          return new T0(2);
        }
      }));
    }),
    _IG/* s1vk9 */ = function(_IH/* s1vka */){
      return E(_IB/* s1vk8 */);
    };
    return new T1(1,function(_II/* s1vkb */){
      return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_II/* s1vkb */, _IG/* s1vk9 */);});
    });
  },
  _IJ/* s1vkd */ = function(_IK/* s1vkf */, _IL/* s1vkg */){
    return new F(function(){return _IM/* s1vke */(_IL/* s1vkg */);});
  },
  _IM/* s1vke */ = function(_IN/* s1vkh */){
    var _IO/* s1vki */ = new T(function(){
      var _IP/* s1vkj */ = new T(function(){
        var _IQ/* s1vkq */ = new T(function(){
          var _IR/* s1vkp */ = function(_IS/* s1vkl */){
            return new F(function(){return _It/* s1vjH */(_8G/* GHC.Types.True */, function(_IT/* s1vkm */){
              return new F(function(){return A1(_IN/* s1vkh */,new T2(1,_IS/* s1vkl */,_IT/* s1vkm */));});
            });});
          };
          return B(A2(_Ir/* s1vjF */,_lS/* Text.ParserCombinators.ReadPrec.minPrec */, _IR/* s1vkp */));
        });
        return B(_9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(_It/* s1vjH */(_4x/* GHC.Types.False */, _IN/* s1vkh */)), _IQ/* s1vkq */));
      });
      return B(_ll/* Text.Read.Lex.expect2 */(function(_IU/* s1vkr */){
        var _IV/* s1vks */ = E(_IU/* s1vkr */);
        return (_IV/* s1vks */._==2) ? (!B(_2n/* GHC.Base.eqString */(_IV/* s1vks */.a, _Ip/* GHC.Read.lvl6 */))) ? new T0(2) : E(_IP/* s1vkj */) : new T0(2);
      }));
    }),
    _IW/* s1vkw */ = function(_IX/* s1vkx */){
      return E(_IO/* s1vki */);
    };
    return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_IY/* s1vky */){
      return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_IY/* s1vky */, _IW/* s1vkw */);});
    }), new T(function(){
      return new T1(1,B(_lT/* GHC.Read.$wa3 */(_IJ/* s1vkd */, _IN/* s1vkh */)));
    }));});
  };
  return new F(function(){return _IM/* s1vke */(_Is/* s1vjG */);});
},
_IZ/* a7 */ = function(_J0/* s1vpn */, _J1/* s1vpo */){
  return new F(function(){return _J2/* GHC.Read.$wa19 */(_J1/* s1vpo */);});
},
_J2/* $wa19 */ = function(_J3/* s1vpp */){
  var _J4/* s1vpu */ = new T(function(){
    return B(_ll/* Text.Read.Lex.expect2 */(function(_J5/* s1vpr */){
      var _J6/* s1vps */ = E(_J5/* s1vpr */);
      if(_J6/* s1vps */._==1){
        return new F(function(){return A1(_J3/* s1vpp */,_J6/* s1vps */.a);});
      }else{
        return new T0(2);
      }
    }));
  }),
  _J7/* s1vpv */ = function(_J8/* s1vpw */){
    return E(_J4/* s1vpu */);
  };
  return new F(function(){return _9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(_9T/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_J9/* s1vpx */){
    return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_J9/* s1vpx */, _J7/* s1vpv */);});
  }), new T(function(){
    return B(_Iq/* GHC.Read.$wa */(_Im/* GHC.Read.$fReadChar2 */, _J3/* s1vpp */));
  }))), new T(function(){
    return new T1(1,B(_lT/* GHC.Read.$wa3 */(_IZ/* GHC.Read.a7 */, _J3/* s1vpp */)));
  }));});
},
_Ja/* $fReadChar1 */ = function(_Jb/* s1vpF */, _Jc/* s1vpG */){
  return new F(function(){return _J2/* GHC.Read.$wa19 */(_Jc/* s1vpG */);});
},
_Jd/* $fRead[]3 */ = function(_Je/* s1vpI */, _Jf/* s1vpJ */){
  return new F(function(){return _Iq/* GHC.Read.$wa */(_Ja/* GHC.Read.$fReadChar1 */, _Jf/* s1vpJ */);});
},
_Jg/* $fRead[]5 */ = new T(function(){
  return B(_Iq/* GHC.Read.$wa */(_Ja/* GHC.Read.$fReadChar1 */, _aZ/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
}),
_Jh/* $fRead[]4 */ = function(_Ji/* B1 */){
  return new F(function(){return _8s/* Text.ParserCombinators.ReadP.run */(_Jg/* GHC.Read.$fRead[]5 */, _Ji/* B1 */);});
},
_Jj/* $fReadChar4 */ = new T(function(){
  return B(_J2/* GHC.Read.$wa19 */(_aZ/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
}),
_Jk/* $fReadChar3 */ = function(_Ji/* B1 */){
  return new F(function(){return _8s/* Text.ParserCombinators.ReadP.run */(_Jj/* GHC.Read.$fReadChar4 */, _Ji/* B1 */);});
},
_Jl/* $fRead[]_$s$creadsPrec1 */ = function(_Jm/* s1vpH */, _Ji/* B1 */){
  return new F(function(){return _Jk/* GHC.Read.$fReadChar3 */(_Ji/* B1 */);});
},
_Jn/* $fRead[]_$s$fRead[]1 */ = new T4(0,_Jl/* GHC.Read.$fRead[]_$s$creadsPrec1 */,_Jh/* GHC.Read.$fRead[]4 */,_Ja/* GHC.Read.$fReadChar1 */,_Jd/* GHC.Read.$fRead[]3 */),
_Jo/* $fShowQuestion2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}"));
}),
_Jp/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("="));
}),
_Jq/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("otherInfo"));
}),
_Jr/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(","));
}),
_Js/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("bookRef"));
}),
_Jt/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("questionId"));
}),
_Ju/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("chapterId"));
}),
_Jv/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("{"));
}),
_Jw/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Question"));
}),
_Jx/* $wa */ = function(_Jy/* sak6 */, _Jz/* sak7 */){
  if(_Jy/* sak6 */>11){
    return new T0(2);
  }else{
    var _JA/* saka */ = new T(function(){
      var _JB/* sakb */ = new T(function(){
        var _JC/* sakc */ = new T(function(){
          var _JD/* sakd */ = new T(function(){
            var _JE/* sake */ = new T(function(){
              var _JF/* sam9 */ = function(_JG/* sakf */){
                var _JH/* sakg */ = new T(function(){
                  var _JI/* sakh */ = new T(function(){
                    var _JJ/* saki */ = new T(function(){
                      var _JK/* sakj */ = new T(function(){
                        var _JL/* salF */ = function(_JM/* sakk */){
                          var _JN/* sakl */ = new T(function(){
                            var _JO/* sakm */ = new T(function(){
                              var _JP/* sakn */ = new T(function(){
                                var _JQ/* sako */ = new T(function(){
                                  var _JR/* salb */ = function(_JS/* sakp */){
                                    var _JT/* sakq */ = new T(function(){
                                      var _JU/* sakr */ = new T(function(){
                                        var _JV/* saks */ = new T(function(){
                                          var _JW/* sakt */ = new T(function(){
                                            var _JX/* sakH */ = function(_JY/* saku */){
                                              var _JZ/* sakv */ = new T(function(){
                                                var _K0/* sakw */ = new T(function(){
                                                  return B(A1(_Jz/* sak7 */,new T4(0,_JG/* sakf */,_JM/* sakk */,_JS/* sakp */,_JY/* saku */)));
                                                });
                                                return B(_ll/* Text.Read.Lex.expect2 */(function(_K1/* saky */){
                                                  var _K2/* sakz */ = E(_K1/* saky */);
                                                  return (_K2/* sakz */._==2) ? (!B(_2n/* GHC.Base.eqString */(_K2/* sakz */.a, _Jo/* Model.Question.$fShowQuestion2 */))) ? new T0(2) : E(_K0/* sakw */) : new T0(2);
                                                }));
                                              }),
                                              _K3/* sakD */ = function(_K4/* sakE */){
                                                return E(_JZ/* sakv */);
                                              };
                                              return new T1(1,function(_K5/* sakF */){
                                                return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_K5/* sakF */, _K3/* sakD */);});
                                              });
                                            };
                                            return B(A3(_HO/* GHC.Read.$fReadMaybe2 */,_Jn/* GHC.Read.$fRead[]_$s$fRead[]1 */, _lS/* Text.ParserCombinators.ReadPrec.minPrec */, _JX/* sakH */));
                                          });
                                          return B(_ll/* Text.Read.Lex.expect2 */(function(_K6/* sakI */){
                                            var _K7/* sakJ */ = E(_K6/* sakI */);
                                            return (_K7/* sakJ */._==2) ? (!B(_2n/* GHC.Base.eqString */(_K7/* sakJ */.a, _Jp/* Model.Question.lvl */))) ? new T0(2) : E(_JW/* sakt */) : new T0(2);
                                          }));
                                        }),
                                        _K8/* sakN */ = function(_K9/* sakO */){
                                          return E(_JV/* saks */);
                                        },
                                        _Ka/* sakP */ = function(_Kb/* sakQ */){
                                          return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Kb/* sakQ */, _K8/* sakN */);});
                                        };
                                        return B(_ll/* Text.Read.Lex.expect2 */(function(_Kc/* sakS */){
                                          var _Kd/* sakT */ = E(_Kc/* sakS */);
                                          return (_Kd/* sakT */._==3) ? (!B(_2n/* GHC.Base.eqString */(_Kd/* sakT */.a, _Jq/* Model.Question.lvl1 */))) ? new T0(2) : E(new T1(1,_Ka/* sakP */)) : new T0(2);
                                        }));
                                      }),
                                      _Ke/* sakX */ = function(_Kf/* sakY */){
                                        return E(_JU/* sakr */);
                                      },
                                      _Kg/* sakZ */ = function(_Kh/* sal0 */){
                                        return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Kh/* sal0 */, _Ke/* sakX */);});
                                      };
                                      return B(_ll/* Text.Read.Lex.expect2 */(function(_Ki/* sal2 */){
                                        var _Kj/* sal3 */ = E(_Ki/* sal2 */);
                                        return (_Kj/* sal3 */._==2) ? (!B(_2n/* GHC.Base.eqString */(_Kj/* sal3 */.a, _Jr/* Model.Question.lvl2 */))) ? new T0(2) : E(new T1(1,_Kg/* sakZ */)) : new T0(2);
                                      }));
                                    }),
                                    _Kk/* sal7 */ = function(_Kl/* sal8 */){
                                      return E(_JT/* sakq */);
                                    };
                                    return new T1(1,function(_Km/* sal9 */){
                                      return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Km/* sal9 */, _Kk/* sal7 */);});
                                    });
                                  };
                                  return B(A3(_HO/* GHC.Read.$fReadMaybe2 */,_Jn/* GHC.Read.$fRead[]_$s$fRead[]1 */, _lS/* Text.ParserCombinators.ReadPrec.minPrec */, _JR/* salb */));
                                });
                                return B(_ll/* Text.Read.Lex.expect2 */(function(_Kn/* salc */){
                                  var _Ko/* sald */ = E(_Kn/* salc */);
                                  return (_Ko/* sald */._==2) ? (!B(_2n/* GHC.Base.eqString */(_Ko/* sald */.a, _Jp/* Model.Question.lvl */))) ? new T0(2) : E(_JQ/* sako */) : new T0(2);
                                }));
                              }),
                              _Kp/* salh */ = function(_Kq/* sali */){
                                return E(_JP/* sakn */);
                              },
                              _Kr/* salj */ = function(_Ks/* salk */){
                                return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Ks/* salk */, _Kp/* salh */);});
                              };
                              return B(_ll/* Text.Read.Lex.expect2 */(function(_Kt/* salm */){
                                var _Ku/* saln */ = E(_Kt/* salm */);
                                return (_Ku/* saln */._==3) ? (!B(_2n/* GHC.Base.eqString */(_Ku/* saln */.a, _Js/* Model.Question.lvl3 */))) ? new T0(2) : E(new T1(1,_Kr/* salj */)) : new T0(2);
                              }));
                            }),
                            _Kv/* salr */ = function(_Kw/* sals */){
                              return E(_JO/* sakm */);
                            },
                            _Kx/* salt */ = function(_Ky/* salu */){
                              return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Ky/* salu */, _Kv/* salr */);});
                            };
                            return B(_ll/* Text.Read.Lex.expect2 */(function(_Kz/* salw */){
                              var _KA/* salx */ = E(_Kz/* salw */);
                              return (_KA/* salx */._==2) ? (!B(_2n/* GHC.Base.eqString */(_KA/* salx */.a, _Jr/* Model.Question.lvl2 */))) ? new T0(2) : E(new T1(1,_Kx/* salt */)) : new T0(2);
                            }));
                          }),
                          _KB/* salB */ = function(_KC/* salC */){
                            return E(_JN/* sakl */);
                          };
                          return new T1(1,function(_KD/* salD */){
                            return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_KD/* salD */, _KB/* salB */);});
                          });
                        };
                        return B(A3(_mn/* GHC.Read.$fReadInt3 */,_mQ/* GHC.Read.$fReadInt_$sconvertInt */, _lS/* Text.ParserCombinators.ReadPrec.minPrec */, _JL/* salF */));
                      });
                      return B(_ll/* Text.Read.Lex.expect2 */(function(_KE/* salG */){
                        var _KF/* salH */ = E(_KE/* salG */);
                        return (_KF/* salH */._==2) ? (!B(_2n/* GHC.Base.eqString */(_KF/* salH */.a, _Jp/* Model.Question.lvl */))) ? new T0(2) : E(_JK/* sakj */) : new T0(2);
                      }));
                    }),
                    _KG/* salL */ = function(_KH/* salM */){
                      return E(_JJ/* saki */);
                    },
                    _KI/* salN */ = function(_KJ/* salO */){
                      return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_KJ/* salO */, _KG/* salL */);});
                    };
                    return B(_ll/* Text.Read.Lex.expect2 */(function(_KK/* salQ */){
                      var _KL/* salR */ = E(_KK/* salQ */);
                      return (_KL/* salR */._==3) ? (!B(_2n/* GHC.Base.eqString */(_KL/* salR */.a, _Jt/* Model.Question.lvl4 */))) ? new T0(2) : E(new T1(1,_KI/* salN */)) : new T0(2);
                    }));
                  }),
                  _KM/* salV */ = function(_KN/* salW */){
                    return E(_JI/* sakh */);
                  },
                  _KO/* salX */ = function(_KP/* salY */){
                    return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_KP/* salY */, _KM/* salV */);});
                  };
                  return B(_ll/* Text.Read.Lex.expect2 */(function(_KQ/* sam0 */){
                    var _KR/* sam1 */ = E(_KQ/* sam0 */);
                    return (_KR/* sam1 */._==2) ? (!B(_2n/* GHC.Base.eqString */(_KR/* sam1 */.a, _Jr/* Model.Question.lvl2 */))) ? new T0(2) : E(new T1(1,_KO/* salX */)) : new T0(2);
                  }));
                }),
                _KS/* sam5 */ = function(_KT/* sam6 */){
                  return E(_JH/* sakg */);
                };
                return new T1(1,function(_KU/* sam7 */){
                  return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_KU/* sam7 */, _KS/* sam5 */);});
                });
              };
              return B(A3(_mn/* GHC.Read.$fReadInt3 */,_mQ/* GHC.Read.$fReadInt_$sconvertInt */, _lS/* Text.ParserCombinators.ReadPrec.minPrec */, _JF/* sam9 */));
            });
            return B(_ll/* Text.Read.Lex.expect2 */(function(_KV/* sama */){
              var _KW/* samb */ = E(_KV/* sama */);
              return (_KW/* samb */._==2) ? (!B(_2n/* GHC.Base.eqString */(_KW/* samb */.a, _Jp/* Model.Question.lvl */))) ? new T0(2) : E(_JE/* sake */) : new T0(2);
            }));
          }),
          _KX/* samf */ = function(_KY/* samg */){
            return E(_JD/* sakd */);
          },
          _KZ/* samh */ = function(_L0/* sami */){
            return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_L0/* sami */, _KX/* samf */);});
          };
          return B(_ll/* Text.Read.Lex.expect2 */(function(_L1/* samk */){
            var _L2/* saml */ = E(_L1/* samk */);
            return (_L2/* saml */._==3) ? (!B(_2n/* GHC.Base.eqString */(_L2/* saml */.a, _Ju/* Model.Question.lvl5 */))) ? new T0(2) : E(new T1(1,_KZ/* samh */)) : new T0(2);
          }));
        }),
        _L3/* samp */ = function(_L4/* samq */){
          return E(_JC/* sakc */);
        },
        _L5/* samr */ = function(_L6/* sams */){
          return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_L6/* sams */, _L3/* samp */);});
        };
        return B(_ll/* Text.Read.Lex.expect2 */(function(_L7/* samu */){
          var _L8/* samv */ = E(_L7/* samu */);
          return (_L8/* samv */._==2) ? (!B(_2n/* GHC.Base.eqString */(_L8/* samv */.a, _Jv/* Model.Question.lvl6 */))) ? new T0(2) : E(new T1(1,_L5/* samr */)) : new T0(2);
        }));
      }),
      _L9/* samz */ = function(_La/* samA */){
        return E(_JB/* sakb */);
      },
      _Lb/* samB */ = function(_Lc/* samC */){
        return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Lc/* samC */, _L9/* samz */);});
      };
      return B(_ll/* Text.Read.Lex.expect2 */(function(_Ld/* samE */){
        var _Le/* samF */ = E(_Ld/* samE */);
        return (_Le/* samF */._==3) ? (!B(_2n/* GHC.Base.eqString */(_Le/* samF */.a, _Jw/* Model.Question.lvl7 */))) ? new T0(2) : E(new T1(1,_Lb/* samB */)) : new T0(2);
      }));
    }),
    _Lf/* samJ */ = function(_Lg/* samK */){
      return E(_JA/* saka */);
    };
    return new T1(1,function(_Lh/* samL */){
      return new F(function(){return A2(_k2/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_Lh/* samL */, _Lf/* samJ */);});
    });
  }
},
_Li/* $fReadQuestion3 */ = function(_Lj/* samN */, _Lk/* samO */){
  return new F(function(){return _Jx/* Model.Question.$wa */(E(_Lj/* samN */), _Lk/* samO */);});
},
_Ll/* lvl2 */ = new T(function(){
  return B(A3(_mc/* GHC.Read.$fReadDouble10 */,_Li/* Model.Question.$fReadQuestion3 */, _lS/* Text.ParserCombinators.ReadPrec.minPrec */, _mX/* Text.Read.readEither5 */));
}),
_Lm/* $wa33 */ = function(_Ln/* slVN */, _Lo/* slVO */, _/* EXTERNAL */){
  var _Lp/* slVY */ = eval/* EXTERNAL */(E(_11/* FormEngine.JQuery.setText2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_Lp/* slVY */), toJSStr/* EXTERNAL */(E(_Ln/* slVN */)), _Lo/* slVO */);});
},
_Lq/* a */ = new T(function(){
  return B(unCStr/* EXTERNAL */("div"));
}),
_Lr/* getHeight_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.height(); })");
}),
_Ls/* getScrollTop_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.scrollTop(); })");
}),
_Lt/* hideJq3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("visibility"));
}),
_Lu/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("body"));
}),
_Lv/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("margin-top"));
}),
_Lw/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No details available"));
}),
_Lx/* overlayId */ = new T(function(){
  return B(unCStr/* EXTERNAL */("overlay"));
}),
_Ly/* selectById2 */ = "(function (id) { return $(\'#\' + id); })",
_Lz/* selectById1 */ = function(_LA/* slKB */, _/* EXTERNAL */){
  var _LB/* slKL */ = eval/* EXTERNAL */(E(_Ly/* FormEngine.JQuery.selectById2 */));
  return new F(function(){return __app1/* EXTERNAL */(E(_LB/* slKL */), toJSStr/* EXTERNAL */(E(_LA/* slKB */)));});
},
_LC/* setHeight_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (val, jq) { jq.height(val); return jq; })");
}),
_LD/* showJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("visible"));
}),
_LE/* overlayOn1 */ = function(_LF/* sEup */, _/* EXTERNAL */){
  var _LG/* sEur */ = B(_Lz/* FormEngine.JQuery.selectById1 */(_Lx/* Overlay.overlayId */, _/* EXTERNAL */)),
  _LH/* sEuu */ = E(_LG/* sEur */),
  _LI/* sEuw */ = B(_t2/* FormEngine.JQuery.$wa9 */(_Lq/* Overlay.a */, _LH/* sEuu */, _/* EXTERNAL */)),
  _LJ/* sEuz */ = function(_/* EXTERNAL */){
    var _LK/* sEuB */ = B(_2E/* FormEngine.JQuery.select1 */(_Lu/* Overlay.lvl */, _/* EXTERNAL */)),
    _LL/* sEuJ */ = __app1/* EXTERNAL */(E(_Lr/* FormEngine.JQuery.getHeight_f1 */), E(_LK/* sEuB */)),
    _LM/* sEuN */ = Number/* EXTERNAL */(_LL/* sEuJ */),
    _LN/* sEuR */ = jsTrunc/* EXTERNAL */(_LM/* sEuN */),
    _LO/* sEuZ */ = __app2/* EXTERNAL */(E(_LC/* FormEngine.JQuery.setHeight_f1 */), _LN/* sEuR */, _LH/* sEuu */),
    _LP/* sEv2 */ = B(_t2/* FormEngine.JQuery.$wa9 */(_Lq/* Overlay.a */, _LH/* sEuu */, _/* EXTERNAL */)),
    _LQ/* sEv5 */ = B(_2E/* FormEngine.JQuery.select1 */(_Lu/* Overlay.lvl */, _/* EXTERNAL */)),
    _LR/* sEvd */ = __app1/* EXTERNAL */(E(_Ls/* FormEngine.JQuery.getScrollTop_f1 */), E(_LQ/* sEv5 */)),
    _LS/* sEvh */ = Number/* EXTERNAL */(_LR/* sEvd */),
    _LT/* sEvl */ = jsTrunc/* EXTERNAL */(_LS/* sEvh */),
    _LU/* sEvs */ = B(_K/* FormEngine.JQuery.$wa2 */(_Lv/* Overlay.lvl1 */, B(_1M/* GHC.Show.$wshowSignedInt */(0, _LT/* sEvl */+25|0, _k/* GHC.Types.[] */)), E(_LP/* sEv2 */), _/* EXTERNAL */));
    return new F(function(){return _K/* FormEngine.JQuery.$wa2 */(_Lt/* FormEngine.JQuery.hideJq3 */, _LD/* FormEngine.JQuery.showJq2 */, _LH/* sEuu */, _/* EXTERNAL */);});
  },
  _LV/* sEvv */ = E(_LF/* sEup */);
  if(!_LV/* sEvv */._){
    var _LW/* sEvy */ = B(_Lm/* FormEngine.JQuery.$wa33 */(_Lw/* Overlay.lvl2 */, E(_LI/* sEuw */), _/* EXTERNAL */));
    return new F(function(){return _LJ/* sEuz */(_/* EXTERNAL */);});
  }else{
    var _LX/* sEvF */ = B(_sX/* FormEngine.JQuery.$wa26 */(_LV/* sEvv */, E(_LI/* sEuw */), _/* EXTERNAL */));
    return new F(function(){return _LJ/* sEuz */(_/* EXTERNAL */);});
  }
},
_LY/* $wlvl */ = function(_LZ/* s4GP */, _/* EXTERNAL */){
  var _M0/* s4GS */ = B(_1A/* FormEngine.FormItem.fiDescriptor */(B(_1D/* FormEngine.FormElement.FormElement.formItem */(_LZ/* s4GP */)))),
  _M1/* s4H4 */ = E(_M0/* s4GS */.g);
  if(!_M1/* s4H4 */._){
    return _0/* GHC.Tuple.() */;
  }else{
    var _M2/* s4H5 */ = _M1/* s4H4 */.a,
    _M3/* s4H6 */ = E(_M0/* s4GS */.h);
    if(!_M3/* s4H6 */._){
      return _0/* GHC.Tuple.() */;
    }else{
      var _M4/* s4H7 */ = _M3/* s4H6 */.a,
      _M5/* s4H8 */ = new T(function(){
        return B(_1M/* GHC.Show.$wshowSignedInt */(0, E(_M2/* s4H5 */), _k/* GHC.Types.[] */));
      }),
      _M6/* s4Hc */ = new T(function(){
        return B(_1M/* GHC.Show.$wshowSignedInt */(0, E(_M4/* s4H7 */), _k/* GHC.Types.[] */));
      }),
      _M7/* s4Io */ = function(_M8/* s4Ho */){
        var _M9/* s4Hp */ = new T(function(){
          var _Ma/* s4Hq */ = E(_M8/* s4Ho */);
          if(!_Ma/* s4Hq */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T1(1,new T(function(){
              var _Mb/* s4Ht */ = B(_8l/* Text.Read.readEither6 */(B(_8s/* Text.ParserCombinators.ReadP.run */(_Ll/* Form.lvl2 */, _Ma/* s4Hq */.a))));
              if(!_Mb/* s4Ht */._){
                return E(_HC/* Form.lvl */);
              }else{
                if(!E(_Mb/* s4Ht */.b)._){
                  return E(_Mb/* s4Ht */.a);
                }else{
                  return E(_HE/* Form.lvl1 */);
                }
              }
            }));
          }
        }),
        _Mc/* s4HI */ = new T2(1,new T(function(){
          var _Md/* s4HB */ = E(_M9/* s4Hp */);
          if(!_Md/* s4HB */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(E(_Md/* s4HB */.a).d);
          }
        }),_k/* GHC.Types.[] */),
        _Me/* s4HJ */ = new T(function(){
          var _Mf/* s4HK */ = E(_M9/* s4Hp */);
          if(!_Mf/* s4HK */._){
            return __Z/* EXTERNAL */;
          }else{
            if(!E(E(_Mf/* s4HK */.a).c)._){
              return __Z/* EXTERNAL */;
            }else{
              return E(_Hy/* Texts.bookAckTxt */);
            }
          }
        }),
        _Mg/* s4HT */ = function(_Mh/* s4HU */){
          var _Mi/* s4HV */ = E(_Mh/* s4HU */);
          if(!_Mi/* s4HV */._){
            return E(_Me/* s4HJ */);
          }else{
            return new F(function(){return _7/* GHC.Base.++ */(_Mi/* s4HV */.a, new T(function(){
              return B(_Mg/* s4HT */(_Mi/* s4HV */.b));
            },1));});
          }
        },
        _Mj/* s4In */ = function(_Mk/* s4HZ */, _/* EXTERNAL */){
          var _Ml/* s4Ij */ = new T(function(){
            var _Mm/* s4I1 */ = E(_M9/* s4Hp */);
            if(!_Mm/* s4I1 */._){
              return B(_Mg/* s4HT */(B(_pe/* Data.Maybe.catMaybes1 */(new T2(1,_Mk/* s4HZ */,_Mc/* s4HI */)))));
            }else{
              var _Mn/* s4Ia */ = E(E(_Mm/* s4I1 */.a).c);
              if(!_Mn/* s4Ia */._){
                return B(_Mg/* s4HT */(B(_pe/* Data.Maybe.catMaybes1 */(new T2(1,_Mk/* s4HZ */,_Mc/* s4HI */)))));
              }else{
                var _Mo/* s4Ii */ = new T(function(){
                  var _Mp/* s4Ih */ = new T(function(){
                    return B(_7/* GHC.Base.++ */(_Hz/* Texts.bookLabelTxt1 */, new T(function(){
                      return B(_Mg/* s4HT */(B(_pe/* Data.Maybe.catMaybes1 */(new T2(1,_Mk/* s4HZ */,_Mc/* s4HI */)))));
                    },1)));
                  },1);
                  return B(_7/* GHC.Base.++ */(_Mn/* s4Ia */.a, _Mp/* s4Ih */));
                },1);
                return B(_7/* GHC.Base.++ */(_HA/* Texts.bookLabelTxt2 */, _Mo/* s4Ii */));
              }
            }
          },1),
          _Mq/* s4Ik */ = B(_LE/* Overlay.overlayOn1 */(_Ml/* s4Ij */, _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        };
        return new F(function(){return _H3/* Haste.Ajax.ajaxRequest */(_GG/* Control.Monad.IO.Class.$fMonadIOIO */, _EE/* Haste.Prim.JSType.$fJSTypeJSString */, _EL/* Haste.Prim.JSType.$fJSType[] */, _EL/* Haste.Prim.JSType.$fJSType[] */, _GH/* Haste.Ajax.POST */, _HI/* Form.lvl19 */, new T2(1,new T2(0,_HG/* Form.lvl17 */,_M5/* s4H8 */),new T2(1,new T2(0,_HH/* Form.lvl18 */,_M6/* s4Hc */),_k/* GHC.Types.[] */)), _Mj/* s4In */);});
      };
      return new F(function(){return A(_H3/* Haste.Ajax.ajaxRequest */,[_GG/* Control.Monad.IO.Class.$fMonadIOIO */, _EE/* Haste.Prim.JSType.$fJSTypeJSString */, _EL/* Haste.Prim.JSType.$fJSType[] */, _EL/* Haste.Prim.JSType.$fJSType[] */, _GH/* Haste.Ajax.POST */, _HF/* Form.lvl16 */, new T2(1,new T2(0,_HG/* Form.lvl17 */,new T(function(){
        return B(_1R/* GHC.Show.$fShowInt_$cshow */(_M2/* s4H5 */));
      })),new T2(1,new T2(0,_HH/* Form.lvl18 */,new T(function(){
        return B(_1R/* GHC.Show.$fShowInt_$cshow */(_M4/* s4H7 */));
      })),_k/* GHC.Types.[] */)), _M7/* s4Io */, _/* EXTERNAL */]);});
    }
  }
},
_Mr/* lvl20 */ = function(_Ms/* s4Ip */, _Mt/* s4Iq */, _/* EXTERNAL */){
  return new F(function(){return _LY/* Form.$wlvl */(_Ms/* s4Ip */, _/* EXTERNAL */);});
},
_Mu/* lvl21 */ = new T2(0,_EB/* Form.lvl15 */,_Mr/* Form.lvl20 */),
_Mv/* lvl22 */ = new T1(1,_Mu/* Form.lvl21 */),
_Mw/* lvl23 */ = new T3(0,_4y/* GHC.Base.Nothing */,_4y/* GHC.Base.Nothing */,_Mv/* Form.lvl22 */),
_Mx/* lvl24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'desc-subpane\'>"));
}),
_My/* lvl25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("id"));
}),
_Mz/* lvl26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\'long-desc\'>"));
}),
_MA/* lvl27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("img/hint-icon.png\' style=\'margin-right: 5px;\'>"));
}),
_MB/* lvl28 */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_Ew/* Config.Config.staticURL */, _MA/* Form.lvl27 */));
}),
_MC/* lvl29 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img src=\'", _MB/* Form.lvl28 */));
}),
_MD/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("textarea"));
}),
_ME/* lvl30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<span/>"));
}),
_MF/* lvl31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#form"));
}),
_MG/* lvl32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("input"));
}),
_MH/* lvl33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("input:checked"));
}),
_MI/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("select"));
}),
_MJ/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'main-pane\'>"));
}),
_MK/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'form-subpane\'>"));
}),
_ML/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("img/valid.png\'/>"));
}),
_MM/* lvl8 */ = new T(function(){
  return B(_7/* GHC.Base.++ */(_Ew/* Config.Config.staticURL */, _ML/* Form.lvl7 */));
}),
_MN/* lvl9 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img alt=\'valid\' class=\'validity-flag\' src=\'", _MM/* Form.lvl8 */));
}),
_MO/* click1 */ = function(_MP/* sly0 */, _/* EXTERNAL */){
  return new F(function(){return _4t/* FormEngine.JQuery.$wa5 */(E(_MP/* sly0 */), _/* EXTERNAL */);});
},
_MQ/* selectTab1 */ = function(_MR/* sh9R */, _MS/* sh9S */, _/* EXTERNAL */){
  var _MT/* sh9X */ = new T(function(){
    return B(_2g/* FormEngine.FormElement.Identifiers.tabId */(new T(function(){
      return B(_5Q/* GHC.List.$w!! */(_MS/* sh9S */, E(_MR/* sh9R */)));
    },1)));
  },1),
  _MU/* sh9Z */ = B(_2E/* FormEngine.JQuery.select1 */(B(_7/* GHC.Base.++ */(_2C/* FormEngine.FormElement.Tabs.colorizeTabs4 */, _MT/* sh9X */)), _/* EXTERNAL */));
  return new F(function(){return _MO/* FormEngine.JQuery.click1 */(_MU/* sh9Z */, _/* EXTERNAL */);});
},
_MV/* generateForm1 */ = function(_MW/* s4Is */, _/* EXTERNAL */){
  var _MX/* s4Iu */ = B(_2E/* FormEngine.JQuery.select1 */(_MF/* Form.lvl31 */, _/* EXTERNAL */)),
  _MY/* s4Iz */ = new T2(1,_4H/* Form.aboutTab */,_MW/* s4Is */),
  _MZ/* s4K8 */ = new T(function(){
    var _N0/* s4K7 */ = function(_N1/* s4IB */, _/* EXTERNAL */){
      var _N2/* s4ID */ = B(_2E/* FormEngine.JQuery.select1 */(_MJ/* Form.lvl5 */, _/* EXTERNAL */)),
      _N3/* s4II */ = B(_X/* FormEngine.JQuery.$wa3 */(_MK/* Form.lvl6 */, E(_N2/* s4ID */), _/* EXTERNAL */)),
      _N4/* s4IN */ = E(_B/* FormEngine.JQuery.addClassInside_f3 */),
      _N5/* s4IQ */ = __app1/* EXTERNAL */(_N4/* s4IN */, E(_N3/* s4II */)),
      _N6/* s4IT */ = E(_A/* FormEngine.JQuery.addClassInside_f2 */),
      _N7/* s4IW */ = __app1/* EXTERNAL */(_N6/* s4IT */, _N5/* s4IQ */),
      _N8/* s4J1 */ = B(_Ej/* FormEngine.FormElement.Rendering.foldElements1 */(B(_l/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_$cchildren */(_N1/* s4IB */)), new T3(0,_MW/* s4Is */,_MN/* Form.lvl9 */,_Ey/* Form.lvl12 */), _Mw/* Form.lvl23 */, _N7/* s4IW */, _/* EXTERNAL */)),
      _N9/* s4J6 */ = E(_z/* FormEngine.JQuery.addClassInside_f1 */),
      _Na/* s4J9 */ = __app1/* EXTERNAL */(_N9/* s4J6 */, E(_N8/* s4J1 */)),
      _Nb/* s4Jc */ = B(_X/* FormEngine.JQuery.$wa3 */(_Mx/* Form.lvl24 */, _Na/* s4J9 */, _/* EXTERNAL */)),
      _Nc/* s4Ji */ = B(_C/* FormEngine.JQuery.$wa20 */(_My/* Form.lvl25 */, new T(function(){
        return B(_4O/* FormEngine.FormElement.Identifiers.descSubpaneId */(_N1/* s4IB */));
      },1), E(_Nb/* s4Jc */), _/* EXTERNAL */)),
      _Nd/* s4Jo */ = __app1/* EXTERNAL */(_N4/* s4IN */, E(_Nc/* s4Ji */)),
      _Ne/* s4Js */ = __app1/* EXTERNAL */(_N6/* s4IT */, _Nd/* s4Jo */),
      _Nf/* s4Jv */ = B(_X/* FormEngine.JQuery.$wa3 */(_Mz/* Form.lvl26 */, _Ne/* s4Js */, _/* EXTERNAL */)),
      _Ng/* s4JB */ = B(_C/* FormEngine.JQuery.$wa20 */(_My/* Form.lvl25 */, new T(function(){
        return B(_4R/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId */(_N1/* s4IB */));
      },1), E(_Nf/* s4Jv */), _/* EXTERNAL */)),
      _Nh/* s4JH */ = __app1/* EXTERNAL */(_N4/* s4IN */, E(_Ng/* s4JB */)),
      _Ni/* s4JL */ = __app1/* EXTERNAL */(_N6/* s4IT */, _Nh/* s4JH */),
      _Nj/* s4JO */ = B(_X/* FormEngine.JQuery.$wa3 */(_MC/* Form.lvl29 */, _Ni/* s4JL */, _/* EXTERNAL */)),
      _Nk/* s4JT */ = B(_X/* FormEngine.JQuery.$wa3 */(_ME/* Form.lvl30 */, E(_Nj/* s4JO */), _/* EXTERNAL */)),
      _Nl/* s4JZ */ = __app1/* EXTERNAL */(_N9/* s4J6 */, E(_Nk/* s4JT */));
      return new F(function(){return __app1/* EXTERNAL */(_N9/* s4J6 */, _Nl/* s4JZ */);});
    };
    return B(_8H/* GHC.Base.map */(_N0/* s4K7 */, _MW/* s4Is */));
  }),
  _Nm/* s4Ka */ = B(_3f/* FormEngine.FormElement.Tabs.$wa */(_MY/* s4Iz */, new T2(1,_4J/* Form.aboutTabPaneJq1 */,_MZ/* s4K8 */), E(_MX/* s4Iu */), _/* EXTERNAL */)),
  _Nn/* s4Kd */ = B(_MQ/* FormEngine.FormElement.Tabs.selectTab1 */(_4z/* Form.aboutTab4 */, _MY/* s4Iz */, _/* EXTERNAL */)),
  _No/* s4Kg */ = B(_2E/* FormEngine.JQuery.select1 */(_MH/* Form.lvl33 */, _/* EXTERNAL */)),
  _Np/* s4Kl */ = B(_4t/* FormEngine.JQuery.$wa5 */(E(_No/* s4Kg */), _/* EXTERNAL */)),
  _Nq/* s4Kq */ = B(_4t/* FormEngine.JQuery.$wa5 */(E(_Np/* s4Kl */), _/* EXTERNAL */)),
  _Nr/* s4Kt */ = B(_2E/* FormEngine.JQuery.select1 */(_MG/* Form.lvl32 */, _/* EXTERNAL */)),
  _Ns/* s4Ky */ = B(_4o/* FormEngine.JQuery.$wa14 */(E(_Nr/* s4Kt */), _/* EXTERNAL */)),
  _Nt/* s4KB */ = B(_2E/* FormEngine.JQuery.select1 */(_MD/* Form.lvl3 */, _/* EXTERNAL */)),
  _Nu/* s4KG */ = B(_4o/* FormEngine.JQuery.$wa14 */(E(_Nt/* s4KB */), _/* EXTERNAL */)),
  _Nv/* s4KJ */ = B(_2E/* FormEngine.JQuery.select1 */(_MI/* Form.lvl4 */, _/* EXTERNAL */)),
  _Nw/* s4KO */ = B(_4o/* FormEngine.JQuery.$wa14 */(E(_Nv/* s4KJ */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_Nx/* hideJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("hidden"));
}),
_Ny/* initOverlay2 */ = function(_Nz/* sEub */, _/* EXTERNAL */){
  var _NA/* sEud */ = B(_Lz/* FormEngine.JQuery.selectById1 */(_Lx/* Overlay.overlayId */, _/* EXTERNAL */)),
  _NB/* sEui */ = B(_K/* FormEngine.JQuery.$wa2 */(_Lt/* FormEngine.JQuery.hideJq3 */, _Nx/* FormEngine.JQuery.hideJq2 */, E(_NA/* sEud */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_NC/* main2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Error generating tabs"));
}),
_ND/* $wgo2 */ = function(_NE/*  s5bx */, _NF/*  s5by */, _NG/*  s5bz */){
  while(1){
    var _NH/*  $wgo2 */ = B((function(_NI/* s5bx */, _NJ/* s5by */, _NK/* s5bz */){
      var _NL/* s5bA */ = E(_NI/* s5bx */);
      if(!_NL/* s5bA */._){
        return new T2(0,_NJ/* s5by */,_NK/* s5bz */);
      }else{
        var _NM/* s5bB */ = _NL/* s5bA */.a,
        _NN/* s5bM */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_NK/* s5bz */, new T2(1,new T(function(){
            return E(B(_NO/* FormEngine.FormItem.$wincrementNumbering */(_NJ/* s5by */, _NM/* s5bB */)).b);
          }),_k/* GHC.Types.[] */)));
        });
        _NE/*  s5bx */ = _NL/* s5bA */.b;
        _NF/*  s5by */ = new T(function(){
          return E(B(_NO/* FormEngine.FormItem.$wincrementNumbering */(_NJ/* s5by */, _NM/* s5bB */)).a);
        });
        _NG/*  s5bz */ = _NN/* s5bM */;
        return __continue/* EXTERNAL */;
      }
    })(_NE/*  s5bx */, _NF/*  s5by */, _NG/*  s5bz */));
    if(_NH/*  $wgo2 */!=__continue/* EXTERNAL */){
      return _NH/*  $wgo2 */;
    }
  }
},
_NP/* $wgo3 */ = function(_NQ/*  s5bN */, _NR/*  s5bO */, _NS/*  s5bP */){
  while(1){
    var _NT/*  $wgo3 */ = B((function(_NU/* s5bN */, _NV/* s5bO */, _NW/* s5bP */){
      var _NX/* s5bQ */ = E(_NU/* s5bN */);
      if(!_NX/* s5bQ */._){
        return new T2(0,_NV/* s5bO */,_NW/* s5bP */);
      }else{
        var _NY/* s5bR */ = _NX/* s5bQ */.a,
        _NZ/* s5c2 */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_NW/* s5bP */, new T2(1,new T(function(){
            return E(B(_NO/* FormEngine.FormItem.$wincrementNumbering */(_NV/* s5bO */, _NY/* s5bR */)).b);
          }),_k/* GHC.Types.[] */)));
        });
        _NQ/*  s5bN */ = _NX/* s5bQ */.b;
        _NR/*  s5bO */ = new T(function(){
          return E(B(_NO/* FormEngine.FormItem.$wincrementNumbering */(_NV/* s5bO */, _NY/* s5bR */)).a);
        });
        _NS/*  s5bP */ = _NZ/* s5c2 */;
        return __continue/* EXTERNAL */;
      }
    })(_NQ/*  s5bN */, _NR/*  s5bO */, _NS/*  s5bP */));
    if(_NT/*  $wgo3 */!=__continue/* EXTERNAL */){
      return _NT/*  $wgo3 */;
    }
  }
},
_O0/* $wgo4 */ = function(_O1/*  s5c3 */, _O2/*  s5c4 */, _O3/*  s5c5 */){
  while(1){
    var _O4/*  $wgo4 */ = B((function(_O5/* s5c3 */, _O6/* s5c4 */, _O7/* s5c5 */){
      var _O8/* s5c6 */ = E(_O5/* s5c3 */);
      if(!_O8/* s5c6 */._){
        return new T2(0,_O6/* s5c4 */,_O7/* s5c5 */);
      }else{
        var _O9/* s5c7 */ = _O8/* s5c6 */.a,
        _Oa/* s5ci */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_O7/* s5c5 */, new T2(1,new T(function(){
            return E(B(_NO/* FormEngine.FormItem.$wincrementNumbering */(_O6/* s5c4 */, _O9/* s5c7 */)).b);
          }),_k/* GHC.Types.[] */)));
        });
        _O1/*  s5c3 */ = _O8/* s5c6 */.b;
        _O2/*  s5c4 */ = new T(function(){
          return E(B(_NO/* FormEngine.FormItem.$wincrementNumbering */(_O6/* s5c4 */, _O9/* s5c7 */)).a);
        });
        _O3/*  s5c5 */ = _Oa/* s5ci */;
        return __continue/* EXTERNAL */;
      }
    })(_O1/*  s5c3 */, _O2/*  s5c4 */, _O3/*  s5c5 */));
    if(_O4/*  $wgo4 */!=__continue/* EXTERNAL */){
      return _O4/*  $wgo4 */;
    }
  }
},
_Ob/* $wgo5 */ = function(_Oc/*  s5cj */, _Od/*  s5ck */, _Oe/*  s5cl */){
  while(1){
    var _Of/*  $wgo5 */ = B((function(_Og/* s5cj */, _Oh/* s5ck */, _Oi/* s5cl */){
      var _Oj/* s5cm */ = E(_Og/* s5cj */);
      if(!_Oj/* s5cm */._){
        return new T2(0,_Oh/* s5ck */,_Oi/* s5cl */);
      }else{
        var _Ok/* s5cn */ = _Oj/* s5cm */.a,
        _Ol/* s5cy */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_Oi/* s5cl */, new T2(1,new T(function(){
            return E(B(_NO/* FormEngine.FormItem.$wincrementNumbering */(_Oh/* s5ck */, _Ok/* s5cn */)).b);
          }),_k/* GHC.Types.[] */)));
        });
        _Oc/*  s5cj */ = _Oj/* s5cm */.b;
        _Od/*  s5ck */ = new T(function(){
          return E(B(_NO/* FormEngine.FormItem.$wincrementNumbering */(_Oh/* s5ck */, _Ok/* s5cn */)).a);
        });
        _Oe/*  s5cl */ = _Ol/* s5cy */;
        return __continue/* EXTERNAL */;
      }
    })(_Oc/*  s5cj */, _Od/*  s5ck */, _Oe/*  s5cl */));
    if(_Of/*  $wgo5 */!=__continue/* EXTERNAL */){
      return _Of/*  $wgo5 */;
    }
  }
},
_Om/* $wgo6 */ = function(_On/*  s5cz */, _Oo/*  s5cA */, _Op/*  s5cB */){
  while(1){
    var _Oq/*  $wgo6 */ = B((function(_Or/* s5cz */, _Os/* s5cA */, _Ot/* s5cB */){
      var _Ou/* s5cC */ = E(_Or/* s5cz */);
      if(!_Ou/* s5cC */._){
        return new T2(0,_Os/* s5cA */,_Ot/* s5cB */);
      }else{
        var _Ov/* s5cD */ = _Ou/* s5cC */.a,
        _Ow/* s5cO */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_Ot/* s5cB */, new T2(1,new T(function(){
            return E(B(_NO/* FormEngine.FormItem.$wincrementNumbering */(_Os/* s5cA */, _Ov/* s5cD */)).b);
          }),_k/* GHC.Types.[] */)));
        });
        _On/*  s5cz */ = _Ou/* s5cC */.b;
        _Oo/*  s5cA */ = new T(function(){
          return E(B(_NO/* FormEngine.FormItem.$wincrementNumbering */(_Os/* s5cA */, _Ov/* s5cD */)).a);
        });
        _Op/*  s5cB */ = _Ow/* s5cO */;
        return __continue/* EXTERNAL */;
      }
    })(_On/*  s5cz */, _Oo/*  s5cA */, _Op/*  s5cB */));
    if(_Oq/*  $wgo6 */!=__continue/* EXTERNAL */){
      return _Oq/*  $wgo6 */;
    }
  }
},
_Ox/* xs */ = new T(function(){
  return new T2(1,_51/* FormEngine.FormItem.$fShowNumbering2 */,_Ox/* FormEngine.FormItem.xs */);
}),
_Oy/* incrementAtLevel */ = function(_Oz/* s5ba */){
  var _OA/* s5bb */ = E(_Oz/* s5ba */);
  if(!_OA/* s5bb */._){
    return __Z/* EXTERNAL */;
  }else{
    var _OB/* s5bc */ = _OA/* s5bb */.a,
    _OC/* s5bd */ = _OA/* s5bb */.b,
    _OD/* s5bw */ = new T(function(){
      var _OE/* s5be */ = E(_OC/* s5bd */),
      _OF/* s5bk */ = new T2(1,new T(function(){
        return B(_5Q/* GHC.List.$w!! */(_OB/* s5bc */, _OE/* s5be */))+1|0;
      }),_Ox/* FormEngine.FormItem.xs */);
      if(0>=_OE/* s5be */){
        return E(_OF/* s5bk */);
      }else{
        var _OG/* s5bn */ = function(_OH/* s5bo */, _OI/* s5bp */){
          var _OJ/* s5bq */ = E(_OH/* s5bo */);
          if(!_OJ/* s5bq */._){
            return E(_OF/* s5bk */);
          }else{
            var _OK/* s5br */ = _OJ/* s5bq */.a,
            _OL/* s5bt */ = E(_OI/* s5bp */);
            return (_OL/* s5bt */==1) ? new T2(1,_OK/* s5br */,_OF/* s5bk */) : new T2(1,_OK/* s5br */,new T(function(){
              return B(_OG/* s5bn */(_OJ/* s5bq */.b, _OL/* s5bt */-1|0));
            }));
          }
        };
        return B(_OG/* s5bn */(_OB/* s5bc */, _OE/* s5be */));
      }
    });
    return new T2(1,_OD/* s5bw */,_OC/* s5bd */);
  }
},
_OM/* $wgo7 */ = function(_ON/*  s5cP */, _OO/*  s5cQ */, _OP/*  s5cR */){
  while(1){
    var _OQ/*  $wgo7 */ = B((function(_OR/* s5cP */, _OS/* s5cQ */, _OT/* s5cR */){
      var _OU/* s5cS */ = E(_OR/* s5cP */);
      if(!_OU/* s5cS */._){
        return new T2(0,_OS/* s5cQ */,_OT/* s5cR */);
      }else{
        var _OV/* s5cU */ = _OU/* s5cS */.b,
        _OW/* s5cV */ = E(_OU/* s5cS */.a);
        if(!_OW/* s5cV */._){
          var _OX/*   s5cQ */ = _OS/* s5cQ */;
          _ON/*  s5cP */ = _OV/* s5cU */;
          _OO/*  s5cQ */ = _OX/*   s5cQ */;
          _OP/*  s5cR */ = new T(function(){
            return B(_7/* GHC.Base.++ */(_OT/* s5cR */, new T2(1,_OW/* s5cV */,_k/* GHC.Types.[] */)));
          });
          return __continue/* EXTERNAL */;
        }else{
          var _OY/* s5dh */ = new T(function(){
            var _OZ/* s5de */ = new T(function(){
              var _P0/* s5da */ = new T(function(){
                var _P1/* s5d3 */ = E(_OS/* s5cQ */);
                if(!_P1/* s5d3 */._){
                  return __Z/* EXTERNAL */;
                }else{
                  return new T2(1,_P1/* s5d3 */.a,new T(function(){
                    return E(_P1/* s5d3 */.b)+1|0;
                  }));
                }
              });
              return E(B(_Om/* FormEngine.FormItem.$wgo6 */(_OW/* s5cV */.c, _P0/* s5da */, _k/* GHC.Types.[] */)).b);
            });
            return B(_7/* GHC.Base.++ */(_OT/* s5cR */, new T2(1,new T3(1,_OS/* s5cQ */,_OW/* s5cV */.b,_OZ/* s5de */),_k/* GHC.Types.[] */)));
          });
          _ON/*  s5cP */ = _OV/* s5cU */;
          _OO/*  s5cQ */ = new T(function(){
            return B(_Oy/* FormEngine.FormItem.incrementAtLevel */(_OS/* s5cQ */));
          });
          _OP/*  s5cR */ = _OY/* s5dh */;
          return __continue/* EXTERNAL */;
        }
      }
    })(_ON/*  s5cP */, _OO/*  s5cQ */, _OP/*  s5cR */));
    if(_OQ/*  $wgo7 */!=__continue/* EXTERNAL */){
      return _OQ/*  $wgo7 */;
    }
  }
},
_NO/* $wincrementNumbering */ = function(_P2/* s5di */, _P3/* s5dj */){
  var _P4/* s5dk */ = E(_P3/* s5dj */);
  switch(_P4/* s5dk */._){
    case 0:
      return new T2(0,new T(function(){
        return B(_Oy/* FormEngine.FormItem.incrementAtLevel */(_P2/* s5di */));
      }),new T1(0,new T(function(){
        var _P5/* s5dn */ = E(_P4/* s5dk */.a);
        return {_:0,a:_P5/* s5dn */.a,b:_P2/* s5di */,c:_P5/* s5dn */.c,d:_P5/* s5dn */.d,e:_P5/* s5dn */.e,f:_P5/* s5dn */.f,g:_P5/* s5dn */.g,h:_P5/* s5dn */.h,i:_P5/* s5dn */.i,j:_P5/* s5dn */.j,k:_P5/* s5dn */.k};
      })));
    case 1:
      return new T2(0,new T(function(){
        return B(_Oy/* FormEngine.FormItem.incrementAtLevel */(_P2/* s5di */));
      }),new T1(1,new T(function(){
        var _P6/* s5dD */ = E(_P4/* s5dk */.a);
        return {_:0,a:_P6/* s5dD */.a,b:_P2/* s5di */,c:_P6/* s5dD */.c,d:_P6/* s5dD */.d,e:_P6/* s5dD */.e,f:_P6/* s5dD */.f,g:_P6/* s5dD */.g,h:_P6/* s5dD */.h,i:_P6/* s5dD */.i,j:_P6/* s5dD */.j,k:_P6/* s5dD */.k};
      })));
    case 2:
      return new T2(0,new T(function(){
        return B(_Oy/* FormEngine.FormItem.incrementAtLevel */(_P2/* s5di */));
      }),new T1(2,new T(function(){
        var _P7/* s5dT */ = E(_P4/* s5dk */.a);
        return {_:0,a:_P7/* s5dT */.a,b:_P2/* s5di */,c:_P7/* s5dT */.c,d:_P7/* s5dT */.d,e:_P7/* s5dT */.e,f:_P7/* s5dT */.f,g:_P7/* s5dT */.g,h:_P7/* s5dT */.h,i:_P7/* s5dT */.i,j:_P7/* s5dT */.j,k:_P7/* s5dT */.k};
      })));
    case 3:
      return new T2(0,new T(function(){
        return B(_Oy/* FormEngine.FormItem.incrementAtLevel */(_P2/* s5di */));
      }),new T2(3,new T(function(){
        var _P8/* s5ea */ = E(_P4/* s5dk */.a);
        return {_:0,a:_P8/* s5ea */.a,b:_P2/* s5di */,c:_P8/* s5ea */.c,d:_P8/* s5ea */.d,e:_P8/* s5ea */.e,f:_P8/* s5ea */.f,g:_P8/* s5ea */.g,h:_P8/* s5ea */.h,i:_P8/* s5ea */.i,j:_P8/* s5ea */.j,k:_P8/* s5ea */.k};
      }),_P4/* s5dk */.b));
    case 4:
      return new T2(0,new T(function(){
        return B(_Oy/* FormEngine.FormItem.incrementAtLevel */(_P2/* s5di */));
      }),new T2(4,new T(function(){
        var _P9/* s5er */ = E(_P4/* s5dk */.a);
        return {_:0,a:_P9/* s5er */.a,b:_P2/* s5di */,c:_P9/* s5er */.c,d:_P9/* s5er */.d,e:_P9/* s5er */.e,f:_P9/* s5er */.f,g:_P9/* s5er */.g,h:_P9/* s5er */.h,i:_P9/* s5er */.i,j:_P9/* s5er */.j,k:_P9/* s5er */.k};
      }),_P4/* s5dk */.b));
    case 5:
      var _Pa/* s5f6 */ = new T(function(){
        var _Pb/* s5f2 */ = new T(function(){
          var _Pc/* s5eV */ = E(_P2/* s5di */);
          if(!_Pc/* s5eV */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_Pc/* s5eV */.a,new T(function(){
              return E(_Pc/* s5eV */.b)+1|0;
            }));
          }
        });
        return E(B(_OM/* FormEngine.FormItem.$wgo7 */(_P4/* s5dk */.b, _Pb/* s5f2 */, _k/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_Oy/* FormEngine.FormItem.incrementAtLevel */(_P2/* s5di */));
      }),new T2(5,new T(function(){
        var _Pd/* s5eI */ = E(_P4/* s5dk */.a);
        return {_:0,a:_Pd/* s5eI */.a,b:_P2/* s5di */,c:_Pd/* s5eI */.c,d:_Pd/* s5eI */.d,e:_Pd/* s5eI */.e,f:_Pd/* s5eI */.f,g:_Pd/* s5eI */.g,h:_Pd/* s5eI */.h,i:_Pd/* s5eI */.i,j:_Pd/* s5eI */.j,k:_Pd/* s5eI */.k};
      }),_Pa/* s5f6 */));
    case 6:
      return new T2(0,new T(function(){
        return B(_Oy/* FormEngine.FormItem.incrementAtLevel */(_P2/* s5di */));
      }),new T2(6,new T(function(){
        var _Pe/* s5fb */ = E(_P4/* s5dk */.a);
        return {_:0,a:_Pe/* s5fb */.a,b:_P2/* s5di */,c:_Pe/* s5fb */.c,d:_Pe/* s5fb */.d,e:_Pe/* s5fb */.e,f:_Pe/* s5fb */.f,g:_Pe/* s5fb */.g,h:_Pe/* s5fb */.h,i:_Pe/* s5fb */.i,j:_Pe/* s5fb */.j,k:_Pe/* s5fb */.k};
      }),_P4/* s5dk */.b));
    case 7:
      var _Pf/* s5fQ */ = new T(function(){
        var _Pg/* s5fM */ = new T(function(){
          var _Ph/* s5fF */ = E(_P2/* s5di */);
          if(!_Ph/* s5fF */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_Ph/* s5fF */.a,new T(function(){
              return E(_Ph/* s5fF */.b)+1|0;
            }));
          }
        });
        return E(B(_Ob/* FormEngine.FormItem.$wgo5 */(_P4/* s5dk */.b, _Pg/* s5fM */, _k/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_Oy/* FormEngine.FormItem.incrementAtLevel */(_P2/* s5di */));
      }),new T2(7,new T(function(){
        var _Pi/* s5fs */ = E(_P4/* s5dk */.a);
        return {_:0,a:_Pi/* s5fs */.a,b:_P2/* s5di */,c:_Pi/* s5fs */.c,d:_Pi/* s5fs */.d,e:_Pi/* s5fs */.e,f:_Pi/* s5fs */.f,g:_Pi/* s5fs */.g,h:_Pi/* s5fs */.h,i:_Pi/* s5fs */.i,j:_Pi/* s5fs */.j,k:_Pi/* s5fs */.k};
      }),_Pf/* s5fQ */));
    case 8:
      var _Pj/* s5go */ = new T(function(){
        var _Pk/* s5gk */ = new T(function(){
          var _Pl/* s5gd */ = E(_P2/* s5di */);
          if(!_Pl/* s5gd */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_Pl/* s5gd */.a,new T(function(){
              return E(_Pl/* s5gd */.b)+1|0;
            }));
          }
        });
        return E(B(_O0/* FormEngine.FormItem.$wgo4 */(_P4/* s5dk */.c, _Pk/* s5gk */, _k/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_Oy/* FormEngine.FormItem.incrementAtLevel */(_P2/* s5di */));
      }),new T3(8,new T(function(){
        var _Pm/* s5fW */ = E(_P4/* s5dk */.a);
        return {_:0,a:_Pm/* s5fW */.a,b:_P2/* s5di */,c:_Pm/* s5fW */.c,d:_Pm/* s5fW */.d,e:_Pm/* s5fW */.e,f:_Pm/* s5fW */.f,g:_Pm/* s5fW */.g,h:_Pm/* s5fW */.h,i:_Pm/* s5fW */.i,j:_Pm/* s5fW */.j,k:_Pm/* s5fW */.k};
      }),new T(function(){
        var _Pn/* s5g9 */ = E(_P2/* s5di */);
        if(!_Pn/* s5g9 */._){
          return E(_51/* FormEngine.FormItem.$fShowNumbering2 */);
        }else{
          return E(_Pn/* s5g9 */.b);
        }
      }),_Pj/* s5go */));
    case 9:
      var _Po/* s5gW */ = new T(function(){
        var _Pp/* s5gS */ = new T(function(){
          var _Pq/* s5gL */ = E(_P2/* s5di */);
          if(!_Pq/* s5gL */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_Pq/* s5gL */.a,new T(function(){
              return E(_Pq/* s5gL */.b)+1|0;
            }));
          }
        });
        return E(B(_NP/* FormEngine.FormItem.$wgo3 */(_P4/* s5dk */.c, _Pp/* s5gS */, _k/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_Oy/* FormEngine.FormItem.incrementAtLevel */(_P2/* s5di */));
      }),new T3(9,new T(function(){
        var _Pr/* s5gu */ = E(_P4/* s5dk */.a);
        return {_:0,a:_Pr/* s5gu */.a,b:_P2/* s5di */,c:_Pr/* s5gu */.c,d:_Pr/* s5gu */.d,e:_Pr/* s5gu */.e,f:_Pr/* s5gu */.f,g:_Pr/* s5gu */.g,h:_Pr/* s5gu */.h,i:_Pr/* s5gu */.i,j:_Pr/* s5gu */.j,k:_Pr/* s5gu */.k};
      }),new T(function(){
        var _Ps/* s5gH */ = E(_P2/* s5di */);
        if(!_Ps/* s5gH */._){
          return E(_51/* FormEngine.FormItem.$fShowNumbering2 */);
        }else{
          return E(_Ps/* s5gH */.b);
        }
      }),_Po/* s5gW */));
    case 10:
      var _Pt/* s5hu */ = new T(function(){
        var _Pu/* s5hq */ = new T(function(){
          var _Pv/* s5hj */ = E(_P2/* s5di */);
          if(!_Pv/* s5hj */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_Pv/* s5hj */.a,new T(function(){
              return E(_Pv/* s5hj */.b)+1|0;
            }));
          }
        });
        return E(B(_ND/* FormEngine.FormItem.$wgo2 */(_P4/* s5dk */.c, _Pu/* s5hq */, _k/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_Oy/* FormEngine.FormItem.incrementAtLevel */(_P2/* s5di */));
      }),new T3(10,new T(function(){
        var _Pw/* s5h2 */ = E(_P4/* s5dk */.a);
        return {_:0,a:_Pw/* s5h2 */.a,b:_P2/* s5di */,c:_Pw/* s5h2 */.c,d:_Pw/* s5h2 */.d,e:_Pw/* s5h2 */.e,f:_Pw/* s5h2 */.f,g:_Pw/* s5h2 */.g,h:_Pw/* s5h2 */.h,i:_Pw/* s5h2 */.i,j:_Pw/* s5h2 */.j,k:_Pw/* s5h2 */.k};
      }),new T(function(){
        var _Px/* s5hf */ = E(_P2/* s5di */);
        if(!_Px/* s5hf */._){
          return E(_51/* FormEngine.FormItem.$fShowNumbering2 */);
        }else{
          return E(_Px/* s5hf */.b);
        }
      }),_Pt/* s5hu */));
    default:
      return new T2(0,_P2/* s5di */,_P4/* s5dk */);
  }
},
_Py/* $wgo1 */ = function(_Pz/*  s5ki */, _PA/*  s5kj */, _PB/*  s5kk */){
  while(1){
    var _PC/*  $wgo1 */ = B((function(_PD/* s5ki */, _PE/* s5kj */, _PF/* s5kk */){
      var _PG/* s5kl */ = E(_PD/* s5ki */);
      if(!_PG/* s5kl */._){
        return new T2(0,_PE/* s5kj */,_PF/* s5kk */);
      }else{
        var _PH/* s5km */ = _PG/* s5kl */.a,
        _PI/* s5kx */ = new T(function(){
          return B(_7/* GHC.Base.++ */(_PF/* s5kk */, new T2(1,new T(function(){
            return E(B(_NO/* FormEngine.FormItem.$wincrementNumbering */(_PE/* s5kj */, _PH/* s5km */)).b);
          }),_k/* GHC.Types.[] */)));
        });
        _Pz/*  s5ki */ = _PG/* s5kl */.b;
        _PA/*  s5kj */ = new T(function(){
          return E(B(_NO/* FormEngine.FormItem.$wincrementNumbering */(_PE/* s5kj */, _PH/* s5km */)).a);
        });
        _PB/*  s5kk */ = _PI/* s5kx */;
        return __continue/* EXTERNAL */;
      }
    })(_Pz/*  s5ki */, _PA/*  s5kj */, _PB/*  s5kk */));
    if(_PC/*  $wgo1 */!=__continue/* EXTERNAL */){
      return _PC/*  $wgo1 */;
    }
  }
},
_PJ/* NoNumbering */ = __Z/* EXTERNAL */,
_PK/* formItems1629 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be collecting experimental data?"));
}),
_PL/* formItems1628 */ = new T1(1,_PK/* Questionnaire.formItems1629 */),
_PM/* formItems87 */ = 1,
_PN/* formItems86 */ = new T1(1,_PM/* Questionnaire.formItems87 */),
_PO/* formItems876 */ = 38,
_PP/* formItems875 */ = new T1(1,_PO/* Questionnaire.formItems876 */),
_PQ/* formItems1627 */ = {_:0,a:_PL/* Questionnaire.formItems1628 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_PP/* Questionnaire.formItems875 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_PR/* formItems21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_PS/* formItems20 */ = new T1(0,_PR/* Questionnaire.formItems21 */),
_PT/* formItems19 */ = new T2(1,_PS/* Questionnaire.formItems20 */,_k/* GHC.Types.[] */),
_PU/* formItems23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_PV/* formItems22 */ = new T1(0,_PU/* Questionnaire.formItems23 */),
_PW/* formItems18 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_PT/* Questionnaire.formItems19 */),
_PX/* formItems1626 */ = new T2(5,_PQ/* Questionnaire.formItems1627 */,_PW/* Questionnaire.formItems18 */),
_PY/* formItems1625 */ = new T2(1,_PX/* Questionnaire.formItems1626 */,_k/* GHC.Types.[] */),
_PZ/* formItems1630 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_PP/* Questionnaire.formItems875 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Q0/* formItems31 */ = 0,
_Q1/* formItems1624 */ = new T3(8,_PZ/* Questionnaire.formItems1630 */,_Q0/* Questionnaire.formItems31 */,_PY/* Questionnaire.formItems1625 */),
_Q2/* formItems1623 */ = new T2(1,_Q1/* Questionnaire.formItems1624 */,_k/* GHC.Types.[] */),
_Q3/* formItems1636 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be storing samples?"));
}),
_Q4/* formItems1635 */ = new T1(1,_Q3/* Questionnaire.formItems1636 */),
_Q5/* formItems934 */ = 33,
_Q6/* formItems933 */ = new T1(1,_Q5/* Questionnaire.formItems934 */),
_Q7/* formItems1634 */ = {_:0,a:_Q4/* Questionnaire.formItems1635 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Q6/* Questionnaire.formItems933 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Q8/* formItems1633 */ = new T2(5,_Q7/* Questionnaire.formItems1634 */,_PW/* Questionnaire.formItems18 */),
_Q9/* formItems1632 */ = new T2(1,_Q8/* Questionnaire.formItems1633 */,_k/* GHC.Types.[] */),
_Qa/* formItems1637 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Q6/* Questionnaire.formItems933 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Qb/* formItems1631 */ = new T3(8,_Qa/* Questionnaire.formItems1637 */,_Q0/* Questionnaire.formItems31 */,_Q9/* Questionnaire.formItems1632 */),
_Qc/* formItems1622 */ = new T2(1,_Qb/* Questionnaire.formItems1631 */,_Q2/* Questionnaire.formItems1623 */),
_Qd/* formItems1654 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be updating the reference data at regular intervals?"));
}),
_Qe/* formItems1653 */ = new T1(1,_Qd/* Questionnaire.formItems1654 */),
_Qf/* formItems1656 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will the release schedule be?"));
}),
_Qg/* formItems1655 */ = new T1(1,_Qf/* Questionnaire.formItems1656 */),
_Qh/* formItems949 */ = 32,
_Qi/* formItems948 */ = new T1(1,_Qh/* Questionnaire.formItems949 */),
_Qj/* formItems1652 */ = {_:0,a:_Qg/* Questionnaire.formItems1655 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Qe/* Questionnaire.formItems1653 */,g:_PN/* Questionnaire.formItems86 */,h:_Qi/* Questionnaire.formItems948 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Qk/* formItems1651 */ = new T1(1,_Qj/* Questionnaire.formItems1652 */),
_Ql/* formItems1650 */ = new T2(1,_Qk/* Questionnaire.formItems1651 */,_k/* GHC.Types.[] */),
_Qm/* formItems1657 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Qi/* Questionnaire.formItems948 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Qn/* formItems1649 */ = new T3(8,_Qm/* Questionnaire.formItems1657 */,_Q0/* Questionnaire.formItems31 */,_Ql/* Questionnaire.formItems1650 */),
_Qo/* formItems1648 */ = new T2(1,_Qn/* Questionnaire.formItems1649 */,_k/* GHC.Types.[] */),
_Qp/* formItems1663 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will maintenance be paid for in the long run? Will you host it yourself or deposit it with a repository? How will you deal with requests for help? And with requests for adding data?"));
}),
_Qq/* formItems1662 */ = new T1(1,_Qp/* Questionnaire.formItems1663 */),
_Qr/* formItems1665 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you maintain it?"));
}),
_Qs/* formItems1664 */ = new T1(1,_Qr/* Questionnaire.formItems1665 */),
_Qt/* formItems968 */ = 31,
_Qu/* formItems967 */ = new T1(1,_Qt/* Questionnaire.formItems968 */),
_Qv/* formItems1661 */ = {_:0,a:_Qs/* Questionnaire.formItems1664 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Qq/* Questionnaire.formItems1662 */,g:_PN/* Questionnaire.formItems86 */,h:_Qu/* Questionnaire.formItems967 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Qw/* formItems1660 */ = new T1(1,_Qv/* Questionnaire.formItems1661 */),
_Qx/* formItems1659 */ = new T2(1,_Qw/* Questionnaire.formItems1660 */,_k/* GHC.Types.[] */),
_Qy/* formItems1666 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Qu/* Questionnaire.formItems967 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Qz/* formItems1658 */ = new T3(8,_Qy/* Questionnaire.formItems1666 */,_Q0/* Questionnaire.formItems31 */,_Qx/* Questionnaire.formItems1659 */),
_QA/* formItems1647 */ = new T2(1,_Qz/* Questionnaire.formItems1658 */,_Qo/* Questionnaire.formItems1648 */),
_QB/* formItems1015 */ = 30,
_QC/* formItems1014 */ = new T1(1,_QB/* Questionnaire.formItems1015 */),
_QD/* formItems1672 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Who will own the rights to the reference data set? Who will be able to use it?"));
}),
_QE/* formItems1671 */ = new T1(1,_QD/* Questionnaire.formItems1672 */),
_QF/* formItems1674 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What will the Intellectual Property be like?"));
}),
_QG/* formItems1673 */ = new T1(1,_QF/* Questionnaire.formItems1674 */),
_QH/* formItems1670 */ = {_:0,a:_QG/* Questionnaire.formItems1673 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_QE/* Questionnaire.formItems1671 */,g:_PN/* Questionnaire.formItems86 */,h:_QC/* Questionnaire.formItems1014 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_QI/* formItems1669 */ = new T1(1,_QH/* Questionnaire.formItems1670 */),
_QJ/* formItems1668 */ = new T2(1,_QI/* Questionnaire.formItems1669 */,_k/* GHC.Types.[] */),
_QK/* formItems1675 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_QC/* Questionnaire.formItems1014 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_QL/* formItems1667 */ = new T3(8,_QK/* Questionnaire.formItems1675 */,_Q0/* Questionnaire.formItems31 */,_QJ/* Questionnaire.formItems1668 */),
_QM/* formItems1646 */ = new T2(1,_QL/* Questionnaire.formItems1667 */,_QA/* Questionnaire.formItems1647 */),
_QN/* formItems983 */ = 29,
_QO/* formItems982 */ = new T1(1,_QN/* Questionnaire.formItems983 */),
_QP/* formItems1676 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_QO/* Questionnaire.formItems982 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_QQ/* formItems1645 */ = new T3(8,_QP/* Questionnaire.formItems1676 */,_Q0/* Questionnaire.formItems31 */,_QM/* Questionnaire.formItems1646 */),
_QR/* formItems1644 */ = new T2(1,_QQ/* Questionnaire.formItems1645 */,_k/* GHC.Types.[] */),
_QS/* formItems1643 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_QR/* Questionnaire.formItems1644 */),
_QT/* formItems1642 */ = new T2(1,_QS/* Questionnaire.formItems1643 */,_k/* GHC.Types.[] */),
_QU/* formItems1641 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_QT/* Questionnaire.formItems1642 */),
_QV/* formItems1679 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Will any of the data that you will be creating form a reference data set for future research (by others)?</p>"));
}),
_QW/* formItems1678 */ = new T1(1,_QV/* Questionnaire.formItems1679 */),
_QX/* formItems1681 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will reference data be created?"));
}),
_QY/* formItems1680 */ = new T1(1,_QX/* Questionnaire.formItems1681 */),
_QZ/* formItems1677 */ = {_:0,a:_QY/* Questionnaire.formItems1680 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_QW/* Questionnaire.formItems1678 */,g:_PN/* Questionnaire.formItems86 */,h:_QO/* Questionnaire.formItems982 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_R0/* formItems1640 */ = new T2(5,_QZ/* Questionnaire.formItems1677 */,_QU/* Questionnaire.formItems1641 */),
_R1/* formItems1639 */ = new T2(1,_R0/* Questionnaire.formItems1640 */,_k/* GHC.Types.[] */),
_R2/* formItems1638 */ = new T3(8,_QP/* Questionnaire.formItems1676 */,_Q0/* Questionnaire.formItems31 */,_R1/* Questionnaire.formItems1639 */),
_R3/* formItems1621 */ = new T2(1,_R2/* Questionnaire.formItems1638 */,_Qc/* Questionnaire.formItems1622 */),
_R4/* formItems1701 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes, I will make sure to make this data available with my results."));
}),
_R5/* formItems1700 */ = new T1(0,_R4/* Questionnaire.formItems1701 */),
_R6/* formItems1699 */ = new T2(1,_R5/* Questionnaire.formItems1700 */,_k/* GHC.Types.[] */),
_R7/* formItems1698 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_R6/* Questionnaire.formItems1699 */),
_R8/* formItems1193 */ = 81,
_R9/* formItems1192 */ = new T1(1,_R8/* Questionnaire.formItems1193 */),
_Ra/* formItems1704 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Some old data may need to be recovered, e.g. from tables in scientific papers or may be punch cards.</p>"));
}),
_Rb/* formItems1703 */ = new T1(1,_Ra/* Questionnaire.formItems1704 */),
_Rc/* formItems1706 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be using data that needs to be (re-)made computer readable first?"));
}),
_Rd/* formItems1705 */ = new T1(1,_Rc/* Questionnaire.formItems1706 */),
_Re/* formItems1702 */ = {_:0,a:_Rd/* Questionnaire.formItems1705 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Rb/* Questionnaire.formItems1703 */,g:_PN/* Questionnaire.formItems86 */,h:_R9/* Questionnaire.formItems1192 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Rf/* formItems1697 */ = new T2(5,_Re/* Questionnaire.formItems1702 */,_R7/* Questionnaire.formItems1698 */),
_Rg/* formItems1696 */ = new T2(1,_Rf/* Questionnaire.formItems1697 */,_k/* GHC.Types.[] */),
_Rh/* formItems1707 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_R9/* Questionnaire.formItems1192 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Ri/* formItems1695 */ = new T3(8,_Rh/* Questionnaire.formItems1707 */,_Q0/* Questionnaire.formItems31 */,_Rg/* Questionnaire.formItems1696 */),
_Rj/* formItems1694 */ = new T2(1,_Ri/* Questionnaire.formItems1695 */,_k/* GHC.Types.[] */),
_Rk/* formItems1429 */ = 16,
_Rl/* formItems1428 */ = new T1(1,_Rk/* Questionnaire.formItems1429 */),
_Rm/* formItems1713 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">If you are combining data from different sources, harmonization may be required. You may need to re-analyse some original data.</p>"));
}),
_Rn/* formItems1712 */ = new T1(1,_Rm/* Questionnaire.formItems1713 */),
_Ro/* formItems1715 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you need to harmonize different sources of existing data?"));
}),
_Rp/* formItems1714 */ = new T1(1,_Ro/* Questionnaire.formItems1715 */),
_Rq/* formItems1711 */ = {_:0,a:_Rp/* Questionnaire.formItems1714 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Rn/* Questionnaire.formItems1712 */,g:_PN/* Questionnaire.formItems86 */,h:_Rl/* Questionnaire.formItems1428 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Rr/* formItems1710 */ = new T2(5,_Rq/* Questionnaire.formItems1711 */,_PW/* Questionnaire.formItems18 */),
_Rs/* formItems1709 */ = new T2(1,_Rr/* Questionnaire.formItems1710 */,_k/* GHC.Types.[] */),
_Rt/* formItems1716 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Rl/* Questionnaire.formItems1428 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Ru/* formItems1708 */ = new T3(8,_Rt/* Questionnaire.formItems1716 */,_Q0/* Questionnaire.formItems31 */,_Rs/* Questionnaire.formItems1709 */),
_Rv/* formItems1693 */ = new T2(1,_Ru/* Questionnaire.formItems1708 */,_Rj/* Questionnaire.formItems1694 */),
_Rw/* formItems1746 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Data sets that have similar but not identical fields or with identical fields that are not consistently filled can be coupled using probabilistic methods. Will you be using such methods?</p>"));
}),
_Rx/* formItems1745 */ = new T1(1,_Rw/* Questionnaire.formItems1746 */),
_Ry/* formItems1748 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you use probabilistic couplings?"));
}),
_Rz/* formItems1747 */ = new T1(1,_Ry/* Questionnaire.formItems1748 */),
_RA/* formItems728 */ = 49,
_RB/* formItems727 */ = new T1(1,_RA/* Questionnaire.formItems728 */),
_RC/* formItems1744 */ = {_:0,a:_Rz/* Questionnaire.formItems1747 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Rx/* Questionnaire.formItems1745 */,g:_PN/* Questionnaire.formItems86 */,h:_RB/* Questionnaire.formItems727 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_RD/* formItems1743 */ = new T2(5,_RC/* Questionnaire.formItems1744 */,_PW/* Questionnaire.formItems18 */),
_RE/* formItems1742 */ = new T2(1,_RD/* Questionnaire.formItems1743 */,_k/* GHC.Types.[] */),
_RF/* formItems1749 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_RB/* Questionnaire.formItems727 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_RG/* formItems1741 */ = new T3(8,_RF/* Questionnaire.formItems1749 */,_Q0/* Questionnaire.formItems31 */,_RE/* Questionnaire.formItems1742 */),
_RH/* formItems1740 */ = new T2(1,_RG/* Questionnaire.formItems1741 */,_k/* GHC.Types.[] */),
_RI/* formItems1755 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What variable(s) will you be using for the coupling?"));
}),
_RJ/* formItems1754 */ = new T1(1,_RI/* Questionnaire.formItems1755 */),
_RK/* formItems739 */ = 48,
_RL/* formItems738 */ = new T1(1,_RK/* Questionnaire.formItems739 */),
_RM/* formItems1753 */ = {_:0,a:_RJ/* Questionnaire.formItems1754 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_RL/* Questionnaire.formItems738 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_RN/* formItems1752 */ = new T1(1,_RM/* Questionnaire.formItems1753 */),
_RO/* formItems1751 */ = new T2(1,_RN/* Questionnaire.formItems1752 */,_k/* GHC.Types.[] */),
_RP/* formItems1756 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_RL/* Questionnaire.formItems738 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_RQ/* formItems1750 */ = new T3(8,_RP/* Questionnaire.formItems1756 */,_Q0/* Questionnaire.formItems31 */,_RO/* Questionnaire.formItems1751 */),
_RR/* formItems1739 */ = new T2(1,_RQ/* Questionnaire.formItems1750 */,_RH/* Questionnaire.formItems1740 */),
_RS/* formItems1763 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Enlarging the group of subjects (union)"));
}),
_RT/* formItems1762 */ = new T1(0,_RS/* Questionnaire.formItems1763 */),
_RU/* formItems1761 */ = new T2(1,_RT/* Questionnaire.formItems1762 */,_k/* GHC.Types.[] */),
_RV/* formItems1765 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("More data about the same subjects (intersection)"));
}),
_RW/* formItems1764 */ = new T1(0,_RV/* Questionnaire.formItems1765 */),
_RX/* formItems1760 */ = new T2(1,_RW/* Questionnaire.formItems1764 */,_RU/* Questionnaire.formItems1761 */),
_RY/* formItems1768 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What is the goal of the coupling?"));
}),
_RZ/* formItems1767 */ = new T1(1,_RY/* Questionnaire.formItems1768 */),
_S0/* formItems747 */ = 47,
_S1/* formItems746 */ = new T1(1,_S0/* Questionnaire.formItems747 */),
_S2/* formItems1766 */ = {_:0,a:_RZ/* Questionnaire.formItems1767 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_S1/* Questionnaire.formItems746 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_S3/* formItems1759 */ = new T2(5,_S2/* Questionnaire.formItems1766 */,_RX/* Questionnaire.formItems1760 */),
_S4/* formItems1758 */ = new T2(1,_S3/* Questionnaire.formItems1759 */,_k/* GHC.Types.[] */),
_S5/* formItems1769 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_S1/* Questionnaire.formItems746 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_S6/* formItems1757 */ = new T3(8,_S5/* Questionnaire.formItems1769 */,_Q0/* Questionnaire.formItems31 */,_S4/* Questionnaire.formItems1758 */),
_S7/* formItems1738 */ = new T2(1,_S6/* Questionnaire.formItems1757 */,_RR/* Questionnaire.formItems1739 */),
_S8/* formItems1775 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sometimes, through the nature of the data sets that are coupled, the coupled set is no longer representative for the whole population (e.g. some fields may only have been filled for people with high blood pressure). This can disturb your research if undetected. How will you make sure this is not happening?"));
}),
_S9/* formItems1774 */ = new T1(1,_S8/* Questionnaire.formItems1775 */),
_Sa/* formItems1777 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you check whether your coupled data are representative of your goal population?"));
}),
_Sb/* formItems1776 */ = new T1(1,_Sa/* Questionnaire.formItems1777 */),
_Sc/* formItems753 */ = 46,
_Sd/* formItems752 */ = new T1(1,_Sc/* Questionnaire.formItems753 */),
_Se/* formItems1773 */ = {_:0,a:_Sb/* Questionnaire.formItems1776 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_S9/* Questionnaire.formItems1774 */,g:_PN/* Questionnaire.formItems86 */,h:_Sd/* Questionnaire.formItems752 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Sf/* formItems1772 */ = new T1(1,_Se/* Questionnaire.formItems1773 */),
_Sg/* formItems1771 */ = new T2(1,_Sf/* Questionnaire.formItems1772 */,_k/* GHC.Types.[] */),
_Sh/* formItems1778 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Sd/* Questionnaire.formItems752 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Si/* formItems1770 */ = new T3(8,_Sh/* Questionnaire.formItems1778 */,_Q0/* Questionnaire.formItems31 */,_Sg/* Questionnaire.formItems1771 */),
_Sj/* formItems1737 */ = new T2(1,_Si/* Questionnaire.formItems1770 */,_S7/* Questionnaire.formItems1738 */),
_Sk/* formItems1784 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is consent available for the couplings?"));
}),
_Sl/* formItems1783 */ = new T1(1,_Sk/* Questionnaire.formItems1784 */),
_Sm/* formItems795 */ = 45,
_Sn/* formItems794 */ = new T1(1,_Sm/* Questionnaire.formItems795 */),
_So/* formItems1782 */ = {_:0,a:_Sl/* Questionnaire.formItems1783 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Sn/* Questionnaire.formItems794 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Sp/* formItems1781 */ = new T2(5,_So/* Questionnaire.formItems1782 */,_PW/* Questionnaire.formItems18 */),
_Sq/* formItems1780 */ = new T2(1,_Sp/* Questionnaire.formItems1781 */,_k/* GHC.Types.[] */),
_Sr/* formItems1785 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Sn/* Questionnaire.formItems794 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Ss/* formItems1779 */ = new T3(8,_Sr/* Questionnaire.formItems1785 */,_Q0/* Questionnaire.formItems31 */,_Sq/* Questionnaire.formItems1780 */),
_St/* formItems1736 */ = new T2(1,_Ss/* Questionnaire.formItems1779 */,_Sj/* Questionnaire.formItems1737 */),
_Su/* formItems1791 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What will be the procedure that is followed? Where will what data be sent? Did a legal advisor look at the procedures?"));
}),
_Sv/* formItems1790 */ = new T1(1,_Su/* Questionnaire.formItems1791 */),
_Sw/* formItems1793 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be using a trusted third party for coupling?"));
}),
_Sx/* formItems1792 */ = new T1(1,_Sw/* Questionnaire.formItems1793 */),
_Sy/* formItems806 */ = 44,
_Sz/* formItems805 */ = new T1(1,_Sy/* Questionnaire.formItems806 */),
_SA/* formItems1789 */ = {_:0,a:_Sx/* Questionnaire.formItems1792 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Sv/* Questionnaire.formItems1790 */,g:_PN/* Questionnaire.formItems86 */,h:_Sz/* Questionnaire.formItems805 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_SB/* formItems1788 */ = new T1(1,_SA/* Questionnaire.formItems1789 */),
_SC/* formItems1787 */ = new T2(1,_SB/* Questionnaire.formItems1788 */,_k/* GHC.Types.[] */),
_SD/* formItems1794 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Sz/* Questionnaire.formItems805 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_SE/* formItems1786 */ = new T3(8,_SD/* Questionnaire.formItems1794 */,_Q0/* Questionnaire.formItems31 */,_SC/* Questionnaire.formItems1787 */),
_SF/* formItems1735 */ = new T2(1,_SE/* Questionnaire.formItems1786 */,_St/* Questionnaire.formItems1736 */),
_SG/* formItems1800 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Data sets that have exactly identical fields that are well filled can be coupled using deterministic methods. Will you be using such methods?</p>"));
}),
_SH/* formItems1799 */ = new T1(1,_SG/* Questionnaire.formItems1800 */),
_SI/* formItems1802 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you use deterministic couplings?"));
}),
_SJ/* formItems1801 */ = new T1(1,_SI/* Questionnaire.formItems1802 */),
_SK/* formItems826 */ = 43,
_SL/* formItems825 */ = new T1(1,_SK/* Questionnaire.formItems826 */),
_SM/* formItems1798 */ = {_:0,a:_SJ/* Questionnaire.formItems1801 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_SH/* Questionnaire.formItems1799 */,g:_PN/* Questionnaire.formItems86 */,h:_SL/* Questionnaire.formItems825 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_SN/* formItems1797 */ = new T2(5,_SM/* Questionnaire.formItems1798 */,_PW/* Questionnaire.formItems18 */),
_SO/* formItems1796 */ = new T2(1,_SN/* Questionnaire.formItems1797 */,_k/* GHC.Types.[] */),
_SP/* formItems1803 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_SL/* Questionnaire.formItems825 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_SQ/* formItems1795 */ = new T3(8,_SP/* Questionnaire.formItems1803 */,_Q0/* Questionnaire.formItems31 */,_SO/* Questionnaire.formItems1796 */),
_SR/* formItems1734 */ = new T2(1,_SQ/* Questionnaire.formItems1795 */,_SF/* Questionnaire.formItems1735 */),
_SS/* formItems835 */ = 42,
_ST/* formItems834 */ = new T1(1,_SS/* Questionnaire.formItems835 */),
_SU/* formItems1804 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_ST/* Questionnaire.formItems834 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_SV/* formItems1733 */ = new T3(8,_SU/* Questionnaire.formItems1804 */,_Q0/* Questionnaire.formItems31 */,_SR/* Questionnaire.formItems1734 */),
_SW/* formItems1732 */ = new T2(1,_SV/* Questionnaire.formItems1733 */,_k/* GHC.Types.[] */),
_SX/* formItems1731 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_SW/* Questionnaire.formItems1732 */),
_SY/* formItems1730 */ = new T2(1,_SX/* Questionnaire.formItems1731 */,_k/* GHC.Types.[] */),
_SZ/* formItems1729 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_SY/* Questionnaire.formItems1730 */),
_T0/* formItems1807 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you couple existing (biobank) data sets?"));
}),
_T1/* formItems1806 */ = new T1(1,_T0/* Questionnaire.formItems1807 */),
_T2/* formItems1805 */ = {_:0,a:_T1/* Questionnaire.formItems1806 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_ST/* Questionnaire.formItems834 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_T3/* formItems1728 */ = new T2(5,_T2/* Questionnaire.formItems1805 */,_SZ/* Questionnaire.formItems1729 */),
_T4/* formItems1727 */ = new T2(1,_T3/* Questionnaire.formItems1728 */,_k/* GHC.Types.[] */),
_T5/* formItems1726 */ = new T3(8,_SU/* Questionnaire.formItems1804 */,_Q0/* Questionnaire.formItems31 */,_T4/* Questionnaire.formItems1727 */),
_T6/* formItems1725 */ = new T2(1,_T5/* Questionnaire.formItems1726 */,_k/* GHC.Types.[] */),
_T7/* formItems1824 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("I will make sure the selected subset will be available together with my results"));
}),
_T8/* formItems1823 */ = new T1(0,_T7/* Questionnaire.formItems1824 */),
_T9/* formItems1822 */ = new T2(1,_T8/* Questionnaire.formItems1823 */,_k/* GHC.Types.[] */),
_Ta/* formItems1826 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Any filtering or selection will be well documented"));
}),
_Tb/* formItems1825 */ = new T1(0,_Ta/* Questionnaire.formItems1826 */),
_Tc/* formItems1821 */ = new T2(1,_Tb/* Questionnaire.formItems1825 */,_T9/* Questionnaire.formItems1822 */),
_Td/* formItems1828 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("I will use the complete data set"));
}),
_Te/* formItems1827 */ = new T1(0,_Td/* Questionnaire.formItems1828 */),
_Tf/* formItems1820 */ = new T2(1,_Te/* Questionnaire.formItems1827 */,_Tc/* Questionnaire.formItems1821 */),
_Tg/* formItems1412 */ = 18,
_Th/* formItems1411 */ = new T1(1,_Tg/* Questionnaire.formItems1412 */),
_Ti/* formItems1831 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">If you use any filtering, how will you make sure that your results will be reproducible by yourself and others at a later time?</p>"));
}),
_Tj/* formItems1830 */ = new T1(1,_Ti/* Questionnaire.formItems1831 */),
_Tk/* formItems1833 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Can you and will you use the complete existing data set?"));
}),
_Tl/* formItems1832 */ = new T1(1,_Tk/* Questionnaire.formItems1833 */),
_Tm/* formItems1829 */ = {_:0,a:_Tl/* Questionnaire.formItems1832 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Tj/* Questionnaire.formItems1830 */,g:_PN/* Questionnaire.formItems86 */,h:_Th/* Questionnaire.formItems1411 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Tn/* formItems1819 */ = new T2(5,_Tm/* Questionnaire.formItems1829 */,_Tf/* Questionnaire.formItems1820 */),
_To/* formItems1818 */ = new T2(1,_Tn/* Questionnaire.formItems1819 */,_k/* GHC.Types.[] */),
_Tp/* formItems1834 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Th/* Questionnaire.formItems1411 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Tq/* formItems1817 */ = new T3(8,_Tp/* Questionnaire.formItems1834 */,_Q0/* Questionnaire.formItems31 */,_To/* Questionnaire.formItems1818 */),
_Tr/* formItems1816 */ = new T2(1,_Tq/* Questionnaire.formItems1817 */,_k/* GHC.Types.[] */),
_Ts/* formItems1841 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("It may change, I will make sure a copy of the version I used will be available with my results"));
}),
_Tt/* formItems1840 */ = new T1(0,_Ts/* Questionnaire.formItems1841 */),
_Tu/* formItems1839 */ = new T2(1,_Tt/* Questionnaire.formItems1840 */,_k/* GHC.Types.[] */),
_Tv/* formItems1843 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("It is a fixed data set, this will not influence reproducibility of my results"));
}),
_Tw/* formItems1842 */ = new T1(0,_Tv/* Questionnaire.formItems1843 */),
_Tx/* formItems1838 */ = new T2(1,_Tw/* Questionnaire.formItems1842 */,_Tu/* Questionnaire.formItems1839 */),
_Ty/* formItems1421 */ = 17,
_Tz/* formItems1420 */ = new T1(1,_Ty/* Questionnaire.formItems1421 */),
_TA/* formItems1846 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Is the data set you will reuse a fixed data set (with a persistent identifier), or is it a data set that is being worked on (by others) and may be updated during your project or after?</p>"));
}),
_TB/* formItems1845 */ = new T1(1,_TA/* Questionnaire.formItems1846 */),
_TC/* formItems1848 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is the data set fixed, or will it be updated in the future?"));
}),
_TD/* formItems1847 */ = new T1(1,_TC/* Questionnaire.formItems1848 */),
_TE/* formItems1844 */ = {_:0,a:_TD/* Questionnaire.formItems1847 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_TB/* Questionnaire.formItems1845 */,g:_PN/* Questionnaire.formItems86 */,h:_Tz/* Questionnaire.formItems1420 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_TF/* formItems1837 */ = new T2(5,_TE/* Questionnaire.formItems1844 */,_Tx/* Questionnaire.formItems1838 */),
_TG/* formItems1836 */ = new T2(1,_TF/* Questionnaire.formItems1837 */,_k/* GHC.Types.[] */),
_TH/* formItems1849 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Tz/* Questionnaire.formItems1420 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_TI/* formItems1835 */ = new T3(8,_TH/* Questionnaire.formItems1849 */,_Q0/* Questionnaire.formItems31 */,_TG/* Questionnaire.formItems1836 */),
_TJ/* formItems1815 */ = new T2(1,_TI/* Questionnaire.formItems1835 */,_Tr/* Questionnaire.formItems1816 */),
_TK/* formItems1856 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("I need to convert it before using"));
}),
_TL/* formItems1855 */ = new T1(0,_TK/* Questionnaire.formItems1856 */),
_TM/* formItems1854 */ = new T2(1,_TL/* Questionnaire.formItems1855 */,_k/* GHC.Types.[] */),
_TN/* formItems1858 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("I can directly use it"));
}),
_TO/* formItems1857 */ = new T1(0,_TN/* Questionnaire.formItems1858 */),
_TP/* formItems1853 */ = new T2(1,_TO/* Questionnaire.formItems1857 */,_TM/* Questionnaire.formItems1854 */),
_TQ/* formItems1450 */ = 15,
_TR/* formItems1449 */ = new T1(1,_TQ/* Questionnaire.formItems1450 */),
_TS/* formItems1861 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Do you know the data format of the data? Is this suitable for your work? Does it need to be converted?</p>"));
}),
_TT/* formItems1860 */ = new T1(1,_TS/* Questionnaire.formItems1861 */),
_TU/* formItems1863 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you knpw in what format the data is available?"));
}),
_TV/* formItems1862 */ = new T1(1,_TU/* Questionnaire.formItems1863 */),
_TW/* formItems1859 */ = {_:0,a:_TV/* Questionnaire.formItems1862 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_TT/* Questionnaire.formItems1860 */,g:_PN/* Questionnaire.formItems86 */,h:_TR/* Questionnaire.formItems1449 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_TX/* formItems1852 */ = new T2(5,_TW/* Questionnaire.formItems1859 */,_TP/* Questionnaire.formItems1853 */),
_TY/* formItems1851 */ = new T2(1,_TX/* Questionnaire.formItems1852 */,_k/* GHC.Types.[] */),
_TZ/* formItems1864 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_TR/* Questionnaire.formItems1449 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_U0/* formItems1850 */ = new T3(8,_TZ/* Questionnaire.formItems1864 */,_Q0/* Questionnaire.formItems31 */,_TY/* Questionnaire.formItems1851 */),
_U1/* formItems1814 */ = new T2(1,_U0/* Questionnaire.formItems1850 */,_TJ/* Questionnaire.formItems1815 */),
_U2/* formItems1872 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will use it online"));
}),
_U3/* formItems1871 */ = new T1(0,_U2/* Questionnaire.formItems1872 */),
_U4/* formItems1870 */ = new T2(1,_U3/* Questionnaire.formItems1871 */,_k/* GHC.Types.[] */),
_U5/* formItems1874 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will make physical copy"));
}),
_U6/* formItems1873 */ = new T1(0,_U5/* Questionnaire.formItems1874 */),
_U7/* formItems1869 */ = new T2(1,_U6/* Questionnaire.formItems1873 */,_U4/* Questionnaire.formItems1870 */),
_U8/* formItems1876 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Already have physical copy"));
}),
_U9/* formItems1875 */ = new T1(0,_U8/* Questionnaire.formItems1876 */),
_Ua/* formItems1868 */ = new T2(1,_U9/* Questionnaire.formItems1875 */,_U7/* Questionnaire.formItems1869 */),
_Ub/* formItems1468 */ = 14,
_Uc/* formItems1467 */ = new T1(1,_Ub/* Questionnaire.formItems1468 */),
_Ud/* formItems1879 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you be accessing the data?"));
}),
_Ue/* formItems1878 */ = new T1(1,_Ud/* Questionnaire.formItems1879 */),
_Uf/* formItems1877 */ = {_:0,a:_Ue/* Questionnaire.formItems1878 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Uc/* Questionnaire.formItems1467 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Ug/* formItems1867 */ = new T2(5,_Uf/* Questionnaire.formItems1877 */,_Ua/* Questionnaire.formItems1868 */),
_Uh/* formItems1866 */ = new T2(1,_Ug/* Questionnaire.formItems1867 */,_k/* GHC.Types.[] */),
_Ui/* formItems1880 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Uc/* Questionnaire.formItems1467 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Uj/* formItems1865 */ = new T3(8,_Ui/* Questionnaire.formItems1880 */,_Q0/* Questionnaire.formItems31 */,_Uh/* Questionnaire.formItems1866 */),
_Uk/* formItems1813 */ = new T2(1,_Uj/* Questionnaire.formItems1865 */,_U1/* Questionnaire.formItems1814 */),
_Ul/* formItems1474 */ = 13,
_Um/* formItems1473 */ = new T1(1,_Ul/* Questionnaire.formItems1474 */),
_Un/* formItems1886 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will any usage restrictions affect your reuse?"));
}),
_Uo/* formItems1885 */ = new T1(1,_Un/* Questionnaire.formItems1886 */),
_Up/* formItems1884 */ = {_:0,a:_Uo/* Questionnaire.formItems1885 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Um/* Questionnaire.formItems1473 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Uq/* formItems1883 */ = new T2(5,_Up/* Questionnaire.formItems1884 */,_PW/* Questionnaire.formItems18 */),
_Ur/* formItems1882 */ = new T2(1,_Uq/* Questionnaire.formItems1883 */,_k/* GHC.Types.[] */),
_Us/* formItems1887 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Um/* Questionnaire.formItems1473 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Ut/* formItems1881 */ = new T3(8,_Us/* Questionnaire.formItems1887 */,_Q0/* Questionnaire.formItems31 */,_Ur/* Questionnaire.formItems1882 */),
_Uu/* formItems1812 */ = new T2(1,_Ut/* Questionnaire.formItems1881 */,_Uk/* Questionnaire.formItems1813 */),
_Uv/* formItems1895 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("New consent needed"));
}),
_Uw/* formItems1894 */ = new T1(0,_Uv/* Questionnaire.formItems1895 */),
_Ux/* formItems1893 */ = new T2(1,_Uw/* Questionnaire.formItems1894 */,_k/* GHC.Types.[] */),
_Uy/* formItems1897 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Existing consent applies"));
}),
_Uz/* formItems1896 */ = new T1(0,_Uy/* Questionnaire.formItems1897 */),
_UA/* formItems1892 */ = new T2(1,_Uz/* Questionnaire.formItems1896 */,_Ux/* Questionnaire.formItems1893 */),
_UB/* formItems1899 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Not applicable"));
}),
_UC/* formItems1898 */ = new T1(0,_UB/* Questionnaire.formItems1899 */),
_UD/* formItems1891 */ = new T2(1,_UC/* Questionnaire.formItems1898 */,_UA/* Questionnaire.formItems1892 */),
_UE/* formItems1488 */ = 12,
_UF/* formItems1487 */ = new T1(1,_UE/* Questionnaire.formItems1488 */),
_UG/* formItems1902 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">If the data that you will re-use is coupled to people, is the informed consent that was originally obtained from those people covering your current research?</p>"));
}),
_UH/* formItems1901 */ = new T1(1,_UG/* Questionnaire.formItems1902 */),
_UI/* formItems1904 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is extenstion of any consent for privacy sensitive data needed?"));
}),
_UJ/* formItems1903 */ = new T1(1,_UI/* Questionnaire.formItems1904 */),
_UK/* formItems1900 */ = {_:0,a:_UJ/* Questionnaire.formItems1903 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_UH/* Questionnaire.formItems1901 */,g:_PN/* Questionnaire.formItems86 */,h:_UF/* Questionnaire.formItems1487 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_UL/* formItems1890 */ = new T2(5,_UK/* Questionnaire.formItems1900 */,_UD/* Questionnaire.formItems1891 */),
_UM/* formItems1889 */ = new T2(1,_UL/* Questionnaire.formItems1890 */,_k/* GHC.Types.[] */),
_UN/* formItems1905 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_UF/* Questionnaire.formItems1487 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_UO/* formItems1888 */ = new T3(8,_UN/* Questionnaire.formItems1905 */,_Q0/* Questionnaire.formItems31 */,_UM/* Questionnaire.formItems1889 */),
_UP/* formItems1811 */ = new T2(1,_UO/* Questionnaire.formItems1888 */,_Uu/* Questionnaire.formItems1812 */),
_UQ/* formItems1913 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We are the owners"));
}),
_UR/* formItems1912 */ = new T1(0,_UQ/* Questionnaire.formItems1913 */),
_US/* formItems1911 */ = new T2(1,_UR/* Questionnaire.formItems1912 */,_k/* GHC.Types.[] */),
_UT/* formItems1910 */ = new T2(1,_PS/* Questionnaire.formItems20 */,_US/* Questionnaire.formItems1911 */),
_UU/* formItems1540 */ = 10,
_UV/* formItems1539 */ = new T1(1,_UU/* Questionnaire.formItems1540 */),
_UW/* formItems1923 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you need to request access to the data"));
}),
_UX/* formItems1922 */ = new T1(1,_UW/* Questionnaire.formItems1923 */),
_UY/* formItems1921 */ = {_:0,a:_UX/* Questionnaire.formItems1922 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_UV/* Questionnaire.formItems1539 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_UZ/* formItems1920 */ = new T2(5,_UY/* Questionnaire.formItems1921 */,_PW/* Questionnaire.formItems18 */),
_V0/* formItems1919 */ = new T2(1,_UZ/* Questionnaire.formItems1920 */,_k/* GHC.Types.[] */),
_V1/* formItems1924 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_UV/* Questionnaire.formItems1539 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_V2/* formItems1918 */ = new T3(8,_V1/* Questionnaire.formItems1924 */,_Q0/* Questionnaire.formItems31 */,_V0/* Questionnaire.formItems1919 */),
_V3/* formItems1917 */ = new T2(1,_V2/* Questionnaire.formItems1918 */,_k/* GHC.Types.[] */),
_V4/* formItems1522 */ = 11,
_V5/* formItems1521 */ = new T1(1,_V4/* Questionnaire.formItems1522 */),
_V6/* formItems1925 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_V5/* Questionnaire.formItems1521 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_V7/* formItems1916 */ = new T3(8,_V6/* Questionnaire.formItems1925 */,_Q0/* Questionnaire.formItems31 */,_V3/* Questionnaire.formItems1917 */),
_V8/* formItems1915 */ = new T2(1,_V7/* Questionnaire.formItems1916 */,_k/* GHC.Types.[] */),
_V9/* formItems1914 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PU/* Questionnaire.formItems23 */,_V8/* Questionnaire.formItems1915 */),
_Va/* formItems1909 */ = new T2(1,_V9/* Questionnaire.formItems1914 */,_UT/* Questionnaire.formItems1910 */),
_Vb/* formItems1928 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will the owners of this data set work with you on this study"));
}),
_Vc/* formItems1927 */ = new T1(1,_Vb/* Questionnaire.formItems1928 */),
_Vd/* formItems1926 */ = {_:0,a:_Vc/* Questionnaire.formItems1927 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_V5/* Questionnaire.formItems1521 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Ve/* formItems1908 */ = new T2(5,_Vd/* Questionnaire.formItems1926 */,_Va/* Questionnaire.formItems1909 */),
_Vf/* formItems1907 */ = new T2(1,_Ve/* Questionnaire.formItems1908 */,_k/* GHC.Types.[] */),
_Vg/* formItems1906 */ = new T3(8,_V6/* Questionnaire.formItems1925 */,_Q0/* Questionnaire.formItems31 */,_Vf/* Questionnaire.formItems1907 */),
_Vh/* formItems1810 */ = new T2(1,_Vg/* Questionnaire.formItems1906 */,_UP/* Questionnaire.formItems1811 */),
_Vi/* formItems1549 */ = 9,
_Vj/* formItems1548 */ = new T1(1,_Vi/* Questionnaire.formItems1549 */),
_Vk/* formItems1934 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Even if you will be producing your own data, you often will also be relying on existing data sets (e.g. from earlier . You may need to integrate your new data with an existing data set or retrieve additional information from related data bases. Will you be doing such things?</p>"));
}),
_Vl/* formItems1933 */ = new T1(1,_Vk/* Questionnaire.formItems1934 */),
_Vm/* formItems1936 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Write each item on new line"));
}),
_Vn/* formItems1935 */ = new T1(1,_Vm/* Questionnaire.formItems1936 */),
_Vo/* formItems1938 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Items"));
}),
_Vp/* formItems1937 */ = new T1(1,_Vo/* Questionnaire.formItems1938 */),
_Vq/* formItems1932 */ = {_:0,a:_Vp/* Questionnaire.formItems1937 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_Vn/* Questionnaire.formItems1935 */,f:_Vl/* Questionnaire.formItems1933 */,g:_PN/* Questionnaire.formItems86 */,h:_Vj/* Questionnaire.formItems1548 */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_Vr/* formItems1931 */ = new T1(1,_Vq/* Questionnaire.formItems1932 */),
_Vs/* formItems1930 */ = new T2(1,_Vr/* Questionnaire.formItems1931 */,_k/* GHC.Types.[] */),
_Vt/* formItems1941 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What existing non-reference data sets will you use?"));
}),
_Vu/* formItems1940 */ = new T1(1,_Vt/* Questionnaire.formItems1941 */),
_Vv/* formItems1939 */ = {_:0,a:_Vu/* Questionnaire.formItems1940 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Vl/* Questionnaire.formItems1933 */,g:_PN/* Questionnaire.formItems86 */,h:_Vj/* Questionnaire.formItems1548 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Vw/* formItems1929 */ = new T3(8,_Vv/* Questionnaire.formItems1939 */,_Q0/* Questionnaire.formItems31 */,_Vs/* Questionnaire.formItems1930 */),
_Vx/* formItems1809 */ = new T2(1,_Vw/* Questionnaire.formItems1929 */,_Vh/* Questionnaire.formItems1810 */),
_Vy/* formItems1942 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Vj/* Questionnaire.formItems1548 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Vz/* formItems1808 */ = new T3(8,_Vy/* Questionnaire.formItems1942 */,_Q0/* Questionnaire.formItems31 */,_Vx/* Questionnaire.formItems1809 */),
_VA/* formItems1724 */ = new T2(1,_Vz/* Questionnaire.formItems1808 */,_T6/* Questionnaire.formItems1725 */),
_VB/* formItems1955 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("The provider keeps old versions around"));
}),
_VC/* formItems1954 */ = new T1(0,_VB/* Questionnaire.formItems1955 */),
_VD/* formItems1953 */ = new T2(1,_VC/* Questionnaire.formItems1954 */,_k/* GHC.Types.[] */),
_VE/* formItems1957 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("I will keep a copy and make it available with my results"));
}),
_VF/* formItems1956 */ = new T1(0,_VE/* Questionnaire.formItems1957 */),
_VG/* formItems1952 */ = new T2(1,_VF/* Questionnaire.formItems1956 */,_VD/* Questionnaire.formItems1953 */),
_VH/* formItems1204 */ = 80,
_VI/* formItems1203 */ = new T1(1,_VH/* Questionnaire.formItems1204 */),
_VJ/* formItems1960 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Will the reference data in the version you use be available to others?</p>"));
}),
_VK/* formItems1959 */ = new T1(1,_VJ/* Questionnaire.formItems1960 */),
_VL/* formItems1962 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you make sure the same reference data will be available to reproduce your results?"));
}),
_VM/* formItems1961 */ = new T1(1,_VL/* Questionnaire.formItems1962 */),
_VN/* formItems1958 */ = {_:0,a:_VM/* Questionnaire.formItems1961 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_VK/* Questionnaire.formItems1959 */,g:_PN/* Questionnaire.formItems86 */,h:_VI/* Questionnaire.formItems1203 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_VO/* formItems1951 */ = new T2(5,_VN/* Questionnaire.formItems1958 */,_VG/* Questionnaire.formItems1952 */),
_VP/* formItems1950 */ = new T2(1,_VO/* Questionnaire.formItems1951 */,_k/* GHC.Types.[] */),
_VQ/* formItems1963 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_VI/* Questionnaire.formItems1203 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_VR/* formItems1949 */ = new T3(8,_VQ/* Questionnaire.formItems1963 */,_Q0/* Questionnaire.formItems31 */,_VP/* Questionnaire.formItems1950 */),
_VS/* formItems1948 */ = new T2(1,_VR/* Questionnaire.formItems1949 */,_k/* GHC.Types.[] */),
_VT/* formItems1981 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("All analyses will be redone with the new version"));
}),
_VU/* formItems1980 */ = new T1(0,_VT/* Questionnaire.formItems1981 */),
_VV/* formItems1979 */ = new T2(1,_VU/* Questionnaire.formItems1980 */,_k/* GHC.Types.[] */),
_VW/* formItems1983 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("New analyses will be done with the new version"));
}),
_VX/* formItems1982 */ = new T1(0,_VW/* Questionnaire.formItems1983 */),
_VY/* formItems1978 */ = new T2(1,_VX/* Questionnaire.formItems1982 */,_VV/* Questionnaire.formItems1979 */),
_VZ/* formItems1994 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("I will use a downloaded version"));
}),
_W0/* formItems1993 */ = new T1(0,_VZ/* Questionnaire.formItems1994 */),
_W1/* formItems1992 */ = new T2(1,_W0/* Questionnaire.formItems1993 */,_VD/* Questionnaire.formItems1953 */),
_W2/* formItems1996 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("I will need it only at the beginning"));
}),
_W3/* formItems1995 */ = new T1(0,_W2/* Questionnaire.formItems1996 */),
_W4/* formItems1991 */ = new T2(1,_W3/* Questionnaire.formItems1995 */,_W1/* Questionnaire.formItems1992 */),
_W5/* formItems1213 */ = 79,
_W6/* formItems1212 */ = new T1(1,_W5/* Questionnaire.formItems1213 */),
_W7/* formItems1999 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Since you want to keep using the old version of the reference data, how will it be available to you?</p>"));
}),
_W8/* formItems1998 */ = new T1(1,_W7/* Questionnaire.formItems1999 */),
_W9/* formItems2001 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will the old version be available?"));
}),
_Wa/* formItems2000 */ = new T1(1,_W9/* Questionnaire.formItems2001 */),
_Wb/* formItems1997 */ = {_:0,a:_Wa/* Questionnaire.formItems2000 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_W8/* Questionnaire.formItems1998 */,g:_PN/* Questionnaire.formItems86 */,h:_W6/* Questionnaire.formItems1212 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Wc/* formItems1990 */ = new T2(5,_Wb/* Questionnaire.formItems1997 */,_W4/* Questionnaire.formItems1991 */),
_Wd/* formItems1989 */ = new T2(1,_Wc/* Questionnaire.formItems1990 */,_k/* GHC.Types.[] */),
_We/* formItems2002 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_W6/* Questionnaire.formItems1212 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Wf/* formItems1988 */ = new T3(8,_We/* Questionnaire.formItems2002 */,_Q0/* Questionnaire.formItems31 */,_Wd/* Questionnaire.formItems1989 */),
_Wg/* formItems1987 */ = new T2(1,_Wf/* Questionnaire.formItems1988 */,_k/* GHC.Types.[] */),
_Wh/* formItems1564 */ = 8,
_Wi/* formItems1563 */ = new T1(1,_Wh/* Questionnaire.formItems1564 */),
_Wj/* formItems2003 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Wi/* Questionnaire.formItems1563 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Wk/* formItems1986 */ = new T3(8,_Wj/* Questionnaire.formItems2003 */,_Q0/* Questionnaire.formItems31 */,_Wg/* Questionnaire.formItems1987 */),
_Wl/* formItems1985 */ = new T2(1,_Wk/* Questionnaire.formItems1986 */,_k/* GHC.Types.[] */),
_Wm/* formItems2004 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will stay with the old version"));
}),
_Wn/* formItems1984 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_Wm/* Questionnaire.formItems2004 */,_Wl/* Questionnaire.formItems1985 */),
_Wo/* formItems1977 */ = new T2(1,_Wn/* Questionnaire.formItems1984 */,_VY/* Questionnaire.formItems1978 */),
_Wp/* formItems2007 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">If the reference changes while you are working on your research project, you need to decide whether you will follow these changes. Most likely that will mean that you have to do some analyses again, so you will need to make sure enough resources are available to do so. You can decide to stay with the version that you started with; this can have the disadvantage that you will not benefit from added information or added consistency.</p>"));
}),
_Wq/* formItems2006 */ = new T1(1,_Wp/* Questionnaire.formItems2007 */),
_Wr/* formItems2009 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you change version if it updates?"));
}),
_Ws/* formItems2008 */ = new T1(1,_Wr/* Questionnaire.formItems2009 */),
_Wt/* formItems2005 */ = {_:0,a:_Ws/* Questionnaire.formItems2008 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Wq/* Questionnaire.formItems2006 */,g:_PN/* Questionnaire.formItems86 */,h:_Wi/* Questionnaire.formItems1563 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Wu/* formItems1976 */ = new T2(5,_Wt/* Questionnaire.formItems2005 */,_Wo/* Questionnaire.formItems1977 */),
_Wv/* formItems1975 */ = new T2(1,_Wu/* Questionnaire.formItems1976 */,_k/* GHC.Types.[] */),
_Ww/* formItems1974 */ = new T3(8,_Wj/* Questionnaire.formItems2003 */,_Q0/* Questionnaire.formItems31 */,_Wv/* Questionnaire.formItems1975 */),
_Wx/* formItems1973 */ = new T2(1,_Ww/* Questionnaire.formItems1974 */,_k/* GHC.Types.[] */),
_Wy/* formItems2015 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("If there are different versions available, you have to decide with all project partners together which version you will be using. Probably you will go for the latest release as of the date of the start of your research project. However, if you have other data from older projects that need to be merged, you may need to consider using the same release you used for a previous project."));
}),
_Wz/* formItems2014 */ = new T1(1,_Wy/* Questionnaire.formItems2015 */),
_WA/* formItems2017 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Which version will you use?"));
}),
_WB/* formItems2016 */ = new T1(1,_WA/* Questionnaire.formItems2017 */),
_WC/* formItems28 */ = 7,
_WD/* formItems27 */ = new T1(1,_WC/* Questionnaire.formItems28 */),
_WE/* formItems2013 */ = {_:0,a:_WB/* Questionnaire.formItems2016 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Wz/* Questionnaire.formItems2014 */,g:_PN/* Questionnaire.formItems86 */,h:_WD/* Questionnaire.formItems27 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_WF/* formItems2012 */ = new T1(1,_WE/* Questionnaire.formItems2013 */),
_WG/* formItems2011 */ = new T2(1,_WF/* Questionnaire.formItems2012 */,_k/* GHC.Types.[] */),
_WH/* formItems2018 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_WD/* Questionnaire.formItems27 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_WI/* formItems2010 */ = new T3(8,_WH/* Questionnaire.formItems2018 */,_Q0/* Questionnaire.formItems31 */,_WG/* Questionnaire.formItems2011 */),
_WJ/* formItems1972 */ = new T2(1,_WI/* Questionnaire.formItems2010 */,_Wx/* Questionnaire.formItems1973 */),
_WK/* formItems26 */ = 6,
_WL/* formItems25 */ = new T1(1,_WK/* Questionnaire.formItems26 */),
_WM/* formItems2019 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_WL/* Questionnaire.formItems25 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_WN/* formItems1971 */ = new T3(8,_WM/* Questionnaire.formItems2019 */,_Q0/* Questionnaire.formItems31 */,_WJ/* Questionnaire.formItems1972 */),
_WO/* formItems1970 */ = new T2(1,_WN/* Questionnaire.formItems1971 */,_k/* GHC.Types.[] */),
_WP/* formItems1969 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_WO/* Questionnaire.formItems1970 */),
_WQ/* formItems1968 */ = new T2(1,_WP/* Questionnaire.formItems1969 */,_k/* GHC.Types.[] */),
_WR/* formItems1967 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_WQ/* Questionnaire.formItems1968 */),
_WS/* formItems2022 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Many reference data sets evolve over time. If the reference data set changes, this may affect your results. If different versions of a reference data set exist, you need to establish your \"version policy\".</p>"));
}),
_WT/* formItems2021 */ = new T1(1,_WS/* Questionnaire.formItems2022 */),
_WU/* formItems2024 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is the reference data resource versioned?"));
}),
_WV/* formItems2023 */ = new T1(1,_WU/* Questionnaire.formItems2024 */),
_WW/* formItems2020 */ = {_:0,a:_WV/* Questionnaire.formItems2023 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_WT/* Questionnaire.formItems2021 */,g:_PN/* Questionnaire.formItems86 */,h:_WL/* Questionnaire.formItems25 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_WX/* formItems1966 */ = new T2(5,_WW/* Questionnaire.formItems2020 */,_WR/* Questionnaire.formItems1967 */),
_WY/* formItems1965 */ = new T2(1,_WX/* Questionnaire.formItems1966 */,_k/* GHC.Types.[] */),
_WZ/* formItems1964 */ = new T3(8,_WM/* Questionnaire.formItems2019 */,_Q0/* Questionnaire.formItems31 */,_WY/* Questionnaire.formItems1965 */),
_X0/* formItems1947 */ = new T2(1,_WZ/* Questionnaire.formItems1964 */,_VS/* Questionnaire.formItems1948 */),
_X1/* formItems2030 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Do you know the data format of the reference data? Is this suitable for your work? Does it need to be converted?</p>"));
}),
_X2/* formItems2029 */ = new T1(1,_X1/* Questionnaire.formItems2030 */),
_X3/* formItems2032 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you knpw in what format the reference data is available?"));
}),
_X4/* formItems2031 */ = new T1(1,_X3/* Questionnaire.formItems2032 */),
_X5/* formItems44 */ = 5,
_X6/* formItems43 */ = new T1(1,_X5/* Questionnaire.formItems44 */),
_X7/* formItems2028 */ = {_:0,a:_X4/* Questionnaire.formItems2031 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_X2/* Questionnaire.formItems2029 */,g:_PN/* Questionnaire.formItems86 */,h:_X6/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_X8/* formItems2027 */ = new T2(5,_X7/* Questionnaire.formItems2028 */,_TP/* Questionnaire.formItems1853 */),
_X9/* formItems2026 */ = new T2(1,_X8/* Questionnaire.formItems2027 */,_k/* GHC.Types.[] */),
_Xa/* formItems2033 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_X6/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Xb/* formItems2025 */ = new T3(8,_Xa/* Questionnaire.formItems2033 */,_Q0/* Questionnaire.formItems31 */,_X9/* Questionnaire.formItems2026 */),
_Xc/* formItems1946 */ = new T2(1,_Xb/* Questionnaire.formItems2025 */,_X0/* Questionnaire.formItems1947 */),
_Xd/* formItems2043 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Figure this out quickly!"));
}),
_Xe/* formItems53 */ = 4,
_Xf/* formItems52 */ = new T1(1,_Xe/* Questionnaire.formItems53 */),
_Xg/* formItems2044 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Xf/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Xh/* formItems2042 */ = new T2(4,_Xg/* Questionnaire.formItems2044 */,_Xd/* Questionnaire.formItems2043 */),
_Xi/* formItems2041 */ = new T2(1,_Xh/* Questionnaire.formItems2042 */,_k/* GHC.Types.[] */),
_Xj/* formItems2040 */ = new T3(8,_Xg/* Questionnaire.formItems2044 */,_Q0/* Questionnaire.formItems31 */,_Xi/* Questionnaire.formItems2041 */),
_Xk/* formItems2039 */ = new T2(1,_Xj/* Questionnaire.formItems2040 */,_k/* GHC.Types.[] */),
_Xl/* formItems2038 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PU/* Questionnaire.formItems23 */,_Xk/* Questionnaire.formItems2039 */),
_Xm/* formItems2037 */ = new T2(1,_Xl/* Questionnaire.formItems2038 */,_PT/* Questionnaire.formItems19 */),
_Xn/* formItems2047 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Do you know where the reference data is available, what the conditions for use are, and how to reference it?</p>"));
}),
_Xo/* formItems2046 */ = new T1(1,_Xn/* Questionnaire.formItems2047 */),
_Xp/* formItems2049 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you know where and how is it available?"));
}),
_Xq/* formItems2048 */ = new T1(1,_Xp/* Questionnaire.formItems2049 */),
_Xr/* formItems2045 */ = {_:0,a:_Xq/* Questionnaire.formItems2048 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Xo/* Questionnaire.formItems2046 */,g:_PN/* Questionnaire.formItems86 */,h:_Xf/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Xs/* formItems2036 */ = new T2(5,_Xr/* Questionnaire.formItems2045 */,_Xm/* Questionnaire.formItems2037 */),
_Xt/* formItems2035 */ = new T2(1,_Xs/* Questionnaire.formItems2036 */,_k/* GHC.Types.[] */),
_Xu/* formItems2034 */ = new T3(8,_Xg/* Questionnaire.formItems2044 */,_Q0/* Questionnaire.formItems31 */,_Xt/* Questionnaire.formItems2035 */),
_Xv/* formItems1945 */ = new T2(1,_Xu/* Questionnaire.formItems2034 */,_Xc/* Questionnaire.formItems1946 */),
_Xw/* formItems2055 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Much of todays data is used in comparison with reference data. A genome for instance is compared with a reference genome to identify genomic variants. If you use reference data, there are several other issues that you should consider. What are the reference data sets that you will use?</p>"));
}),
_Xx/* formItems2054 */ = new T1(1,_Xw/* Questionnaire.formItems2055 */),
_Xy/* formItems62 */ = 3,
_Xz/* formItems61 */ = new T1(1,_Xy/* Questionnaire.formItems62 */),
_XA/* formItems2053 */ = {_:0,a:_Vp/* Questionnaire.formItems1937 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_Vn/* Questionnaire.formItems1935 */,f:_Xx/* Questionnaire.formItems2054 */,g:_PN/* Questionnaire.formItems86 */,h:_Xz/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_XB/* formItems2052 */ = new T1(1,_XA/* Questionnaire.formItems2053 */),
_XC/* formItems2051 */ = new T2(1,_XB/* Questionnaire.formItems2052 */,_k/* GHC.Types.[] */),
_XD/* formItems2058 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What reference data will you use?"));
}),
_XE/* formItems2057 */ = new T1(1,_XD/* Questionnaire.formItems2058 */),
_XF/* formItems2056 */ = {_:0,a:_XE/* Questionnaire.formItems2057 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Xx/* Questionnaire.formItems2054 */,g:_PN/* Questionnaire.formItems86 */,h:_Xz/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_XG/* formItems2050 */ = new T3(8,_XF/* Questionnaire.formItems2056 */,_Q0/* Questionnaire.formItems31 */,_XC/* Questionnaire.formItems2051 */),
_XH/* formItems1944 */ = new T2(1,_XG/* Questionnaire.formItems2050 */,_Xv/* Questionnaire.formItems1945 */),
_XI/* formItems2059 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_Xz/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_XJ/* formItems1943 */ = new T3(8,_XI/* Questionnaire.formItems2059 */,_Q0/* Questionnaire.formItems31 */,_XH/* Questionnaire.formItems1944 */),
_XK/* formItems1723 */ = new T2(1,_XJ/* Questionnaire.formItems1943 */,_VA/* Questionnaire.formItems1724 */),
_XL/* formItems71 */ = 2,
_XM/* formItems70 */ = new T1(1,_XL/* Questionnaire.formItems71 */),
_XN/* formItems2060 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_XM/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_XO/* formItems1722 */ = new T3(8,_XN/* Questionnaire.formItems2060 */,_Q0/* Questionnaire.formItems31 */,_XK/* Questionnaire.formItems1723 */),
_XP/* formItems1721 */ = new T2(1,_XO/* Questionnaire.formItems1722 */,_k/* GHC.Types.[] */),
_XQ/* formItems1720 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_XP/* Questionnaire.formItems1721 */),
_XR/* formItems1719 */ = new T2(1,_XQ/* Questionnaire.formItems1720 */,_k/* GHC.Types.[] */),
_XS/* formItems2066 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Did you research all the data that exists? You may not be aware of all existing data that could be available. Although using and/or integrating existing data sets may pose a challenge, it will normally be cheaper than collecting everything yourself. Even if you decide not to use an existing data set, it is better to do this as a conscious decision."));
}),
_XT/* formItems2065 */ = new T2(4,_XN/* Questionnaire.formItems2060 */,_XS/* Questionnaire.formItems2066 */),
_XU/* formItems2064 */ = new T2(1,_XT/* Questionnaire.formItems2065 */,_k/* GHC.Types.[] */),
_XV/* formItems2063 */ = new T3(8,_XN/* Questionnaire.formItems2060 */,_Q0/* Questionnaire.formItems31 */,_XU/* Questionnaire.formItems2064 */),
_XW/* formItems2062 */ = new T2(1,_XV/* Questionnaire.formItems2063 */,_k/* GHC.Types.[] */),
_XX/* formItems2061 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PU/* Questionnaire.formItems23 */,_XW/* Questionnaire.formItems2062 */),
_XY/* formItems1718 */ = new T2(1,_XX/* Questionnaire.formItems2061 */,_XR/* Questionnaire.formItems1719 */),
_XZ/* formItems2069 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Will you be referring to any earlier measured data, reference data, or data that should be mined from existing literature? Your own data as well as data from others?</p>"));
}),
_Y0/* formItems2068 */ = new T1(1,_XZ/* Questionnaire.formItems2069 */),
_Y1/* formItems2071 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be using any pre-existing data (including other people\'s data)?"));
}),
_Y2/* formItems2070 */ = new T1(1,_Y1/* Questionnaire.formItems2071 */),
_Y3/* formItems2067 */ = {_:0,a:_Y2/* Questionnaire.formItems2070 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Y0/* Questionnaire.formItems2068 */,g:_PN/* Questionnaire.formItems86 */,h:_XM/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Y4/* formItems1717 */ = new T2(5,_Y3/* Questionnaire.formItems2067 */,_XY/* Questionnaire.formItems1718 */),
_Y5/* formItems1692 */ = new T2(1,_Y4/* Questionnaire.formItems1717 */,_Rv/* Questionnaire.formItems1693 */),
_Y6/* formItems1691 */ = new T3(8,_XN/* Questionnaire.formItems2060 */,_Q0/* Questionnaire.formItems31 */,_Y5/* Questionnaire.formItems1692 */),
_Y7/* formItems1690 */ = new T2(1,_Y6/* Questionnaire.formItems1691 */,_k/* GHC.Types.[] */),
_Y8/* formItems2072 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_PN/* Questionnaire.formItems86 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Y9/* formItems1689 */ = new T3(8,_Y8/* Questionnaire.formItems2072 */,_Q0/* Questionnaire.formItems31 */,_Y7/* Questionnaire.formItems1690 */),
_Ya/* formItems1688 */ = new T2(1,_Y9/* Questionnaire.formItems1689 */,_k/* GHC.Types.[] */),
_Yb/* formItems1687 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_Ya/* Questionnaire.formItems1688 */),
_Yc/* formItems1686 */ = new T2(1,_Yb/* Questionnaire.formItems1687 */,_k/* GHC.Types.[] */),
_Yd/* formItems2078 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("You know that this is very unlikely? This question is not only about data sets that are similar to what you want to determine yourself, but also reference data or data that should be mined from the existing literature. Further, it is very likely that you will refer to related data, e.g. other databases where you usually \"quickly look something up\", but that could maybe be properly integrated, especially if you need to do such lookups multiple times."));
}),
_Ye/* formItems2077 */ = new T2(4,_Y8/* Questionnaire.formItems2072 */,_Yd/* Questionnaire.formItems2078 */),
_Yf/* formItems2076 */ = new T2(1,_Ye/* Questionnaire.formItems2077 */,_k/* GHC.Types.[] */),
_Yg/* formItems2075 */ = new T3(8,_Y8/* Questionnaire.formItems2072 */,_Q0/* Questionnaire.formItems31 */,_Yf/* Questionnaire.formItems2076 */),
_Yh/* formItems2074 */ = new T2(1,_Yg/* Questionnaire.formItems2075 */,_k/* GHC.Types.[] */),
_Yi/* formItems2073 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PU/* Questionnaire.formItems23 */,_Yh/* Questionnaire.formItems2074 */),
_Yj/* formItems1685 */ = new T2(1,_Yi/* Questionnaire.formItems2073 */,_Yc/* Questionnaire.formItems1686 */),
_Yk/* formItems2081 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Are there any data sets available in the world that are relevant to your planned research?</p>"));
}),
_Yl/* formItems2080 */ = new T1(1,_Yk/* Questionnaire.formItems2081 */),
_Ym/* formItems2083 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is there any pre-existing data?"));
}),
_Yn/* formItems2082 */ = new T1(1,_Ym/* Questionnaire.formItems2083 */),
_Yo/* formItems2079 */ = {_:0,a:_Yn/* Questionnaire.formItems2082 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_Yl/* Questionnaire.formItems2080 */,g:_PN/* Questionnaire.formItems86 */,h:_PN/* Questionnaire.formItems86 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Yp/* formItems1684 */ = new T2(5,_Yo/* Questionnaire.formItems2079 */,_Yj/* Questionnaire.formItems1685 */),
_Yq/* formItems1683 */ = new T2(1,_Yp/* Questionnaire.formItems1684 */,_k/* GHC.Types.[] */),
_Yr/* formItems1682 */ = new T3(8,_Y8/* Questionnaire.formItems2072 */,_Q0/* Questionnaire.formItems31 */,_Yq/* Questionnaire.formItems1683 */),
_Ys/* formItems1620 */ = new T2(1,_Yr/* Questionnaire.formItems1682 */,_R3/* Questionnaire.formItems1621 */),
_Yt/* formItems2085 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Before you decide to embark on any new study, it is nowadays good practice to consider all options to keep the data generation part of your study as limited as possible. It is not because we can generate massive amounts of data that we always need to do so. Creating data with public money is bringing with it the responsibility to treat those data well and (if potentially useful) make them available for re-use by others."));
}),
_Yu/* formItems2086 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Yv/* formItems2084 */ = new T2(4,_Yu/* Questionnaire.formItems2086 */,_Yt/* Questionnaire.formItems2085 */),
_Yw/* formItems1619 */ = new T2(1,_Yv/* Questionnaire.formItems2084 */,_Ys/* Questionnaire.formItems1620 */),
_Yx/* formItems2089 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Design of experiment"));
}),
_Yy/* formItems2088 */ = new T1(1,_Yx/* Questionnaire.formItems2089 */),
_Yz/* formItems2087 */ = {_:0,a:_Yy/* Questionnaire.formItems2088 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_PN/* Questionnaire.formItems86 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_YA/* formItems1618 */ = new T2(7,_Yz/* Questionnaire.formItems2087 */,_Yw/* Questionnaire.formItems1619 */),
_YB/* formItems1617 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data design and planning"));
}),
_YC/* formItems1616 */ = new T1(1,_YB/* Questionnaire.formItems1617 */),
_YD/* formItems1615 */ = {_:0,a:_YC/* Questionnaire.formItems1616 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_YE/* formItems1613 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("In the data design and planning phase, we will make sure that we know what data comes when, that we have enough storage space and compute power to deal with it, and that all the responsibilities have been taken care of."));
}),
_YF/* formItems1614 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_YG/* formItems1612 */ = new T2(4,_YF/* Questionnaire.formItems1614 */,_YE/* Questionnaire.formItems1613 */),
_YH/* formItems1603 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes, I will make sure to use common formats for common data types"));
}),
_YI/* formItems1602 */ = new T1(0,_YH/* Questionnaire.formItems1603 */),
_YJ/* formItems1601 */ = new T2(1,_YI/* Questionnaire.formItems1602 */,_k/* GHC.Types.[] */),
_YK/* formItems1605 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No, I am not using any common data types"));
}),
_YL/* formItems1604 */ = new T1(0,_YK/* Questionnaire.formItems1605 */),
_YM/* formItems1600 */ = new T2(1,_YL/* Questionnaire.formItems1604 */,_YJ/* Questionnaire.formItems1601 */),
_YN/* formItems1608 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Some types of data (e.g. genetic variants in the life sciences) are used by many different projects. For such data, often common standards exist that help to make these data reusable. Are you using such common data formats?</p>"));
}),
_YO/* formItems1607 */ = new T1(1,_YN/* Questionnaire.formItems1608 */),
_YP/* formItems1610 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Have you identified types of data that you will use that are used by others too?"));
}),
_YQ/* formItems1609 */ = new T1(1,_YP/* Questionnaire.formItems1610 */),
_YR/* formItems1606 */ = {_:0,a:_YQ/* Questionnaire.formItems1609 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_YO/* Questionnaire.formItems1607 */,g:_XM/* Questionnaire.formItems70 */,h:_PN/* Questionnaire.formItems86 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_YS/* formItems1599 */ = new T2(5,_YR/* Questionnaire.formItems1606 */,_YM/* Questionnaire.formItems1600 */),
_YT/* formItems1598 */ = new T2(1,_YS/* Questionnaire.formItems1599 */,_k/* GHC.Types.[] */),
_YU/* formItems1611 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_PN/* Questionnaire.formItems86 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_YV/* formItems1597 */ = new T3(8,_YU/* Questionnaire.formItems1611 */,_Q0/* Questionnaire.formItems31 */,_YT/* Questionnaire.formItems1598 */),
_YW/* formItems1517 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes, I will register my standards at a data standards registry"));
}),
_YX/* formItems1516 */ = new T1(0,_YW/* Questionnaire.formItems1517 */),
_YY/* formItems1515 */ = new T2(1,_YX/* Questionnaire.formItems1516 */,_k/* GHC.Types.[] */),
_YZ/* formItems1519 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No, this is not needed"));
}),
_Z0/* formItems1518 */ = new T1(0,_YZ/* Questionnaire.formItems1519 */),
_Z1/* formItems1514 */ = new T2(1,_Z0/* Questionnaire.formItems1518 */,_YY/* Questionnaire.formItems1515 */),
_Z2/* formItems1524 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you describe your new data format for others?"));
}),
_Z3/* formItems1523 */ = new T1(1,_Z2/* Questionnaire.formItems1524 */),
_Z4/* formItems1520 */ = {_:0,a:_Z3/* Questionnaire.formItems1523 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_V5/* Questionnaire.formItems1521 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Z5/* formItems1513 */ = new T2(5,_Z4/* Questionnaire.formItems1520 */,_Z1/* Questionnaire.formItems1514 */),
_Z6/* formItems1512 */ = new T2(1,_Z5/* Questionnaire.formItems1513 */,_k/* GHC.Types.[] */),
_Z7/* formItems1525 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_V5/* Questionnaire.formItems1521 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Z8/* formItems1511 */ = new T3(8,_Z7/* Questionnaire.formItems1525 */,_Q0/* Questionnaire.formItems31 */,_Z6/* Questionnaire.formItems1512 */),
_Z9/* formItems1510 */ = new T2(1,_Z8/* Questionnaire.formItems1511 */,_k/* GHC.Types.[] */),
_Za/* formItems1533 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("I will use a completely custom data format"));
}),
_Zb/* formItems1532 */ = new T1(0,_Za/* Questionnaire.formItems1533 */),
_Zc/* formItems1531 */ = new T2(1,_Zb/* Questionnaire.formItems1532 */,_k/* GHC.Types.[] */),
_Zd/* formItems1535 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("I will use a Linked Data format"));
}),
_Ze/* formItems1534 */ = new T1(0,_Zd/* Questionnaire.formItems1535 */),
_Zf/* formItems1530 */ = new T2(1,_Ze/* Questionnaire.formItems1534 */,_Zc/* Questionnaire.formItems1531 */),
_Zg/* formItems1537 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("There is a closely related more generic and open format that I can specialize"));
}),
_Zh/* formItems1536 */ = new T1(0,_Zg/* Questionnaire.formItems1537 */),
_Zi/* formItems1529 */ = new T2(1,_Zh/* Questionnaire.formItems1536 */,_Zf/* Questionnaire.formItems1530 */),
_Zj/* formItems1542 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you design your new data format?"));
}),
_Zk/* formItems1541 */ = new T1(1,_Zj/* Questionnaire.formItems1542 */),
_Zl/* formItems1538 */ = {_:0,a:_Zk/* Questionnaire.formItems1541 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_UV/* Questionnaire.formItems1539 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Zm/* formItems1528 */ = new T2(5,_Zl/* Questionnaire.formItems1538 */,_Zi/* Questionnaire.formItems1529 */),
_Zn/* formItems1527 */ = new T2(1,_Zm/* Questionnaire.formItems1528 */,_k/* GHC.Types.[] */),
_Zo/* formItems1543 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_UV/* Questionnaire.formItems1539 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Zp/* formItems1526 */ = new T3(8,_Zo/* Questionnaire.formItems1543 */,_Q0/* Questionnaire.formItems31 */,_Zn/* Questionnaire.formItems1527 */),
_Zq/* formItems1509 */ = new T2(1,_Zp/* Questionnaire.formItems1526 */,_Z9/* Questionnaire.formItems1510 */),
_Zr/* formItems1551 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Which data type registries will you use?"));
}),
_Zs/* formItems1550 */ = new T1(1,_Zr/* Questionnaire.formItems1551 */),
_Zt/* formItems1547 */ = {_:0,a:_Zs/* Questionnaire.formItems1550 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Vj/* Questionnaire.formItems1548 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Zu/* formItems1546 */ = new T1(1,_Zt/* Questionnaire.formItems1547 */),
_Zv/* formItems1545 */ = new T2(1,_Zu/* Questionnaire.formItems1546 */,_k/* GHC.Types.[] */),
_Zw/* formItems1552 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Vj/* Questionnaire.formItems1548 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_Zx/* formItems1544 */ = new T3(8,_Zw/* Questionnaire.formItems1552 */,_Q0/* Questionnaire.formItems31 */,_Zv/* Questionnaire.formItems1545 */),
_Zy/* formItems1508 */ = new T2(1,_Zx/* Questionnaire.formItems1544 */,_Zq/* Questionnaire.formItems1509 */),
_Zz/* formItems1559 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes, I will make and publish a vocabulary or ontology for some of my data"));
}),
_ZA/* formItems1558 */ = new T1(0,_Zz/* Questionnaire.formItems1559 */),
_ZB/* formItems1557 */ = new T2(1,_ZA/* Questionnaire.formItems1558 */,_k/* GHC.Types.[] */),
_ZC/* formItems1561 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No, suitable public controlled vocabularies or ontologies exist for all of my data types"));
}),
_ZD/* formItems1560 */ = new T1(0,_ZC/* Questionnaire.formItems1561 */),
_ZE/* formItems1556 */ = new T2(1,_ZD/* Questionnaire.formItems1560 */,_ZB/* Questionnaire.formItems1557 */),
_ZF/* formItems1566 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">For good interoperability the use of controlled vocabularies for each discrete data item is advisable. If such vocabularies exist, it is best to reuse those.</p>"));
}),
_ZG/* formItems1565 */ = new T1(1,_ZF/* Questionnaire.formItems1566 */),
_ZH/* formItems1568 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you need to create vocabularies or ontologies for any of your data items?"));
}),
_ZI/* formItems1567 */ = new T1(1,_ZH/* Questionnaire.formItems1568 */),
_ZJ/* formItems1562 */ = {_:0,a:_ZI/* Questionnaire.formItems1567 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_ZG/* Questionnaire.formItems1565 */,g:_XM/* Questionnaire.formItems70 */,h:_Wi/* Questionnaire.formItems1563 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_ZK/* formItems1555 */ = new T2(5,_ZJ/* Questionnaire.formItems1562 */,_ZE/* Questionnaire.formItems1556 */),
_ZL/* formItems1554 */ = new T2(1,_ZK/* Questionnaire.formItems1555 */,_k/* GHC.Types.[] */),
_ZM/* formItems1569 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Wi/* Questionnaire.formItems1563 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_ZN/* formItems1553 */ = new T3(8,_ZM/* Questionnaire.formItems1569 */,_Q0/* Questionnaire.formItems31 */,_ZL/* Questionnaire.formItems1554 */),
_ZO/* formItems1507 */ = new T2(1,_ZN/* Questionnaire.formItems1553 */,_Zy/* Questionnaire.formItems1508 */),
_ZP/* formItems1577 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes, I will create my own data type registry"));
}),
_ZQ/* formItems1576 */ = new T1(0,_ZP/* Questionnaire.formItems1577 */),
_ZR/* formItems1575 */ = new T2(1,_ZQ/* Questionnaire.formItems1576 */,_k/* GHC.Types.[] */),
_ZS/* formItems1579 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes, I will add new types to an existing data type registry"));
}),
_ZT/* formItems1578 */ = new T1(0,_ZS/* Questionnaire.formItems1579 */),
_ZU/* formItems1574 */ = new T2(1,_ZT/* Questionnaire.formItems1578 */,_ZR/* Questionnaire.formItems1575 */),
_ZV/* formItems1581 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No, all of my data types are described in a data type registry already"));
}),
_ZW/* formItems1580 */ = new T1(0,_ZV/* Questionnaire.formItems1581 */),
_ZX/* formItems1573 */ = new T2(1,_ZW/* Questionnaire.formItems1580 */,_ZU/* Questionnaire.formItems1574 */),
_ZY/* formItems1584 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Even if the data format you are using is unique to your project, the discrete data items should be reused or reusable as much as possible. Data type registries can help with that.</p>"));
}),
_ZZ/* formItems1583 */ = new T1(1,_ZY/* Questionnaire.formItems1584 */),
_100/* formItems1586 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you need to add fields in your data format to a data type registry?"));
}),
_101/* formItems1585 */ = new T1(1,_100/* Questionnaire.formItems1586 */),
_102/* formItems1582 */ = {_:0,a:_101/* Questionnaire.formItems1585 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_ZZ/* Questionnaire.formItems1583 */,g:_XM/* Questionnaire.formItems70 */,h:_WD/* Questionnaire.formItems27 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_103/* formItems1572 */ = new T2(5,_102/* Questionnaire.formItems1582 */,_ZX/* Questionnaire.formItems1573 */),
_104/* formItems1571 */ = new T2(1,_103/* Questionnaire.formItems1572 */,_k/* GHC.Types.[] */),
_105/* formItems1587 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_WD/* Questionnaire.formItems27 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_106/* formItems1570 */ = new T3(8,_105/* Questionnaire.formItems1587 */,_Q0/* Questionnaire.formItems31 */,_104/* Questionnaire.formItems1571 */),
_107/* formItems1506 */ = new T2(1,_106/* Questionnaire.formItems1570 */,_ZO/* Questionnaire.formItems1507 */),
_108/* formItems1588 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_XM/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_109/* formItems1505 */ = new T3(8,_108/* Questionnaire.formItems1588 */,_Q0/* Questionnaire.formItems31 */,_107/* Questionnaire.formItems1506 */),
_10a/* formItems1504 */ = new T2(1,_109/* Questionnaire.formItems1505 */,_k/* GHC.Types.[] */),
_10b/* formItems1589 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes, I will need to use custom formats for some of my data"));
}),
_10c/* formItems1503 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_10b/* Questionnaire.formItems1589 */,_10a/* Questionnaire.formItems1504 */),
_10d/* formItems1502 */ = new T2(1,_10c/* Questionnaire.formItems1503 */,_k/* GHC.Types.[] */),
_10e/* formItems1591 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No, all of my data will fit in common formats"));
}),
_10f/* formItems1590 */ = new T1(0,_10e/* Questionnaire.formItems1591 */),
_10g/* formItems1501 */ = new T2(1,_10f/* Questionnaire.formItems1590 */,_10d/* Questionnaire.formItems1502 */),
_10h/* formItems1594 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Sometimes the type of data you collect can not be stored in a commonly used data format. In such cases you may need to make your own, keeping interoperability as high as possible.</p>"));
}),
_10i/* formItems1593 */ = new T1(1,_10h/* Questionnaire.formItems1594 */),
_10j/* formItems1596 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be using new types of data?"));
}),
_10k/* formItems1595 */ = new T1(1,_10j/* Questionnaire.formItems1596 */),
_10l/* formItems1592 */ = {_:0,a:_10k/* Questionnaire.formItems1595 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_10i/* Questionnaire.formItems1593 */,g:_XM/* Questionnaire.formItems70 */,h:_XM/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_10m/* formItems1500 */ = new T2(5,_10l/* Questionnaire.formItems1592 */,_10g/* Questionnaire.formItems1501 */),
_10n/* formItems1499 */ = new T2(1,_10m/* Questionnaire.formItems1500 */,_k/* GHC.Types.[] */),
_10o/* formItems1498 */ = new T3(8,_108/* Questionnaire.formItems1588 */,_Q0/* Questionnaire.formItems31 */,_10n/* Questionnaire.formItems1499 */),
_10p/* formItems1311 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes, all metadata is also explicitly available elsewhere"));
}),
_10q/* formItems1310 */ = new T1(0,_10p/* Questionnaire.formItems1311 */),
_10r/* formItems1309 */ = new T2(1,_10q/* Questionnaire.formItems1310 */,_k/* GHC.Types.[] */),
_10s/* formItems1313 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No, the file names in the project are an essential part of the metadata"));
}),
_10t/* formItems1312 */ = new T1(0,_10s/* Questionnaire.formItems1313 */),
_10u/* formItems1308 */ = new T2(1,_10t/* Questionnaire.formItems1312 */,_10r/* Questionnaire.formItems1309 */),
_10v/* formItems1316 */ = 25,
_10w/* formItems1315 */ = new T1(1,_10v/* Questionnaire.formItems1316 */),
_10x/* formItems1318 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">The file names are very useful as metadata for people involved in the project, but to computers they are just identifiers. To prevent accidents with e.g. renamed files metadata information should always also be available elsewhere and not only through the file name.</p>"));
}),
_10y/* formItems1317 */ = new T1(1,_10x/* Questionnaire.formItems1318 */),
_10z/* formItems1320 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will all the metadata in the file names also be available in the proper metadata?"));
}),
_10A/* formItems1319 */ = new T1(1,_10z/* Questionnaire.formItems1320 */),
_10B/* formItems1314 */ = {_:0,a:_10A/* Questionnaire.formItems1319 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_10y/* Questionnaire.formItems1317 */,g:_XM/* Questionnaire.formItems70 */,h:_10w/* Questionnaire.formItems1315 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_10C/* formItems1307 */ = new T2(5,_10B/* Questionnaire.formItems1314 */,_10u/* Questionnaire.formItems1308 */),
_10D/* formItems1306 */ = new T2(1,_10C/* Questionnaire.formItems1307 */,_k/* GHC.Types.[] */),
_10E/* formItems1321 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_10w/* Questionnaire.formItems1315 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_10F/* formItems1305 */ = new T3(8,_10E/* Questionnaire.formItems1321 */,_Q0/* Questionnaire.formItems31 */,_10D/* Questionnaire.formItems1306 */),
_10G/* formItems1304 */ = new T2(1,_10F/* Questionnaire.formItems1305 */,_k/* GHC.Types.[] */),
_10H/* formItems1327 */ = 24,
_10I/* formItems1326 */ = new T1(1,_10H/* Questionnaire.formItems1327 */),
_10J/* formItems1329 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Advice: Use the same identifiers for sample IDs etc throughout the entire project.</p>"));
}),
_10K/* formItems1328 */ = new T1(1,_10J/* Questionnaire.formItems1329 */),
_10L/* formItems1331 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be keeping the relationships between data clear in the file names?"));
}),
_10M/* formItems1330 */ = new T1(1,_10L/* Questionnaire.formItems1331 */),
_10N/* formItems1325 */ = {_:0,a:_10M/* Questionnaire.formItems1330 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_10K/* Questionnaire.formItems1328 */,g:_XM/* Questionnaire.formItems70 */,h:_10I/* Questionnaire.formItems1326 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_10O/* formItems1324 */ = new T2(5,_10N/* Questionnaire.formItems1325 */,_PW/* Questionnaire.formItems18 */),
_10P/* formItems1323 */ = new T2(1,_10O/* Questionnaire.formItems1324 */,_k/* GHC.Types.[] */),
_10Q/* formItems1332 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_10I/* Questionnaire.formItems1326 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_10R/* formItems1322 */ = new T3(8,_10Q/* Questionnaire.formItems1332 */,_Q0/* Questionnaire.formItems31 */,_10P/* Questionnaire.formItems1323 */),
_10S/* formItems1303 */ = new T2(1,_10R/* Questionnaire.formItems1322 */,_10G/* Questionnaire.formItems1304 */),
_10T/* formItems1338 */ = 23,
_10U/* formItems1337 */ = new T1(1,_10T/* Questionnaire.formItems1338 */),
_10V/* formItems1340 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">It can help if everyone in the project uses the same naming scheme.</p>"));
}),
_10W/* formItems1339 */ = new T1(1,_10V/* Questionnaire.formItems1340 */),
_10X/* formItems1342 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Did you make a SOP (Standard Operating Procedure) for file naming?"));
}),
_10Y/* formItems1341 */ = new T1(1,_10X/* Questionnaire.formItems1342 */),
_10Z/* formItems1336 */ = {_:0,a:_10Y/* Questionnaire.formItems1341 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_10W/* Questionnaire.formItems1339 */,g:_XM/* Questionnaire.formItems70 */,h:_10U/* Questionnaire.formItems1337 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_110/* formItems1335 */ = new T2(5,_10Z/* Questionnaire.formItems1336 */,_PW/* Questionnaire.formItems18 */),
_111/* formItems1334 */ = new T2(1,_110/* Questionnaire.formItems1335 */,_k/* GHC.Types.[] */),
_112/* formItems1343 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_10U/* Questionnaire.formItems1337 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_113/* formItems1333 */ = new T3(8,_112/* Questionnaire.formItems1343 */,_Q0/* Questionnaire.formItems31 */,_111/* Questionnaire.formItems1334 */),
_114/* formItems1302 */ = new T2(1,_113/* Questionnaire.formItems1333 */,_10S/* Questionnaire.formItems1303 */),
_115/* formItems1346 */ = 22,
_116/* formItems1345 */ = new T1(1,_115/* Questionnaire.formItems1346 */),
_117/* formItems1344 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_116/* Questionnaire.formItems1345 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_118/* formItems1301 */ = new T3(8,_117/* Questionnaire.formItems1344 */,_Q0/* Questionnaire.formItems31 */,_114/* Questionnaire.formItems1302 */),
_119/* formItems1300 */ = new T2(1,_118/* Questionnaire.formItems1301 */,_k/* GHC.Types.[] */),
_11a/* formItems432 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Explore"));
}),
_11b/* formItems1299 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_11a/* Questionnaire.formItems432 */,_119/* Questionnaire.formItems1300 */),
_11c/* formItems1298 */ = new T2(1,_11b/* Questionnaire.formItems1299 */,_k/* GHC.Types.[] */),
_11d/* formItems41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Skip"));
}),
_11e/* formItems40 */ = new T1(0,_11d/* Questionnaire.formItems41 */),
_11f/* formItems1297 */ = new T2(1,_11e/* Questionnaire.formItems40 */,_11c/* Questionnaire.formItems1298 */),
_11g/* formItems1349 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Putting some thoughts into file naming can save a lot of trouble later.</p>"));
}),
_11h/* formItems1348 */ = new T1(1,_11g/* Questionnaire.formItems1349 */),
_11i/* formItems1351 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you do file naming and file organization?"));
}),
_11j/* formItems1350 */ = new T1(1,_11i/* Questionnaire.formItems1351 */),
_11k/* formItems1347 */ = {_:0,a:_11j/* Questionnaire.formItems1350 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_11h/* Questionnaire.formItems1348 */,g:_XM/* Questionnaire.formItems70 */,h:_116/* Questionnaire.formItems1345 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_11l/* formItems1296 */ = new T2(5,_11k/* Questionnaire.formItems1347 */,_11f/* Questionnaire.formItems1297 */),
_11m/* formItems1295 */ = new T2(1,_11l/* Questionnaire.formItems1296 */,_k/* GHC.Types.[] */),
_11n/* formItems1294 */ = new T3(8,_117/* Questionnaire.formItems1344 */,_Q0/* Questionnaire.formItems31 */,_11m/* Questionnaire.formItems1295 */),
_11o/* formItems1293 */ = new T2(1,_11n/* Questionnaire.formItems1294 */,_k/* GHC.Types.[] */),
_11p/* formItems1358 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Our work flow system documents the provenance automatically and completely"));
}),
_11q/* formItems1357 */ = new T1(0,_11p/* Questionnaire.formItems1358 */),
_11r/* formItems1356 */ = new T2(1,_11q/* Questionnaire.formItems1357 */,_k/* GHC.Types.[] */),
_11s/* formItems1360 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("All steps will be documented in an (electronic) lab notebook"));
}),
_11t/* formItems1359 */ = new T1(0,_11s/* Questionnaire.formItems1360 */),
_11u/* formItems1355 */ = new T2(1,_11t/* Questionnaire.formItems1359 */,_11r/* Questionnaire.formItems1356 */),
_11v/* formItems1363 */ = 21,
_11w/* formItems1362 */ = new T1(1,_11v/* Questionnaire.formItems1363 */),
_11x/* formItems1365 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">To make your experiments reproducible, all steps in the data processing must be documented in detail. The software you used, including version number, all options and parameters. This information together for every step of the analysis is part of the so-called data provenance. There are more questions regarding this in the chapter on data processing and curation.</p>"));
}),
_11y/* formItems1364 */ = new T1(1,_11x/* Questionnaire.formItems1365 */),
_11z/* formItems1367 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you keep provenance?"));
}),
_11A/* formItems1366 */ = new T1(1,_11z/* Questionnaire.formItems1367 */),
_11B/* formItems1361 */ = {_:0,a:_11A/* Questionnaire.formItems1366 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_11y/* Questionnaire.formItems1364 */,g:_XM/* Questionnaire.formItems70 */,h:_11w/* Questionnaire.formItems1362 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_11C/* formItems1354 */ = new T2(5,_11B/* Questionnaire.formItems1361 */,_11u/* Questionnaire.formItems1355 */),
_11D/* formItems1353 */ = new T2(1,_11C/* Questionnaire.formItems1354 */,_k/* GHC.Types.[] */),
_11E/* formItems1368 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_11w/* Questionnaire.formItems1362 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_11F/* formItems1352 */ = new T3(8,_11E/* Questionnaire.formItems1368 */,_Q0/* Questionnaire.formItems31 */,_11D/* Questionnaire.formItems1353 */),
_11G/* formItems1292 */ = new T2(1,_11F/* Questionnaire.formItems1352 */,_11o/* Questionnaire.formItems1293 */),
_11H/* formItems1383 */ = 19,
_11I/* formItems1382 */ = new T1(1,_11H/* Questionnaire.formItems1383 */),
_11J/* formItems1385 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">It is very likely that data will be moved and copied. At some point people may lose track of the origins. It can be helpful to have the licenses (of coarse as open as possible) stored in close association with the data.</p>"));
}),
_11K/* formItems1384 */ = new T1(1,_11J/* Questionnaire.formItems1385 */),
_11L/* formItems1387 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you store the licenses with the data at all time?"));
}),
_11M/* formItems1386 */ = new T1(1,_11L/* Questionnaire.formItems1387 */),
_11N/* formItems1381 */ = {_:0,a:_11M/* Questionnaire.formItems1386 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_11K/* Questionnaire.formItems1384 */,g:_XM/* Questionnaire.formItems70 */,h:_11I/* Questionnaire.formItems1382 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_11O/* formItems1380 */ = new T2(5,_11N/* Questionnaire.formItems1381 */,_PW/* Questionnaire.formItems18 */),
_11P/* formItems1379 */ = new T2(1,_11O/* Questionnaire.formItems1380 */,_k/* GHC.Types.[] */),
_11Q/* formItems1388 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_11I/* Questionnaire.formItems1382 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_11R/* formItems1378 */ = new T3(8,_11Q/* Questionnaire.formItems1388 */,_Q0/* Questionnaire.formItems31 */,_11P/* Questionnaire.formItems1379 */),
_11S/* formItems1377 */ = new T2(1,_11R/* Questionnaire.formItems1378 */,_k/* GHC.Types.[] */),
_11T/* formItems1391 */ = 20,
_11U/* formItems1390 */ = new T1(1,_11T/* Questionnaire.formItems1391 */),
_11V/* formItems1389 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_11U/* Questionnaire.formItems1390 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_11W/* formItems1376 */ = new T3(8,_11V/* Questionnaire.formItems1389 */,_Q0/* Questionnaire.formItems31 */,_11S/* Questionnaire.formItems1377 */),
_11X/* formItems1375 */ = new T2(1,_11W/* Questionnaire.formItems1376 */,_k/* GHC.Types.[] */),
_11Y/* formItems1374 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_11X/* Questionnaire.formItems1375 */),
_11Z/* formItems1373 */ = new T2(1,_11Y/* Questionnaire.formItems1374 */,_k/* GHC.Types.[] */),
_120/* formItems1372 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_11Z/* Questionnaire.formItems1373 */),
_121/* formItems1394 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">It is not always clear to everyone in the project (ad outside) what can and can not be done with a data set. It is helpful to associate each data set with a license as early as possible in the project. A data license should ideally be as free as possible: any restriction like \'only for non-commercial use\' or \'attribution required\' may reduce the reusability and thereby the number of citations. If possible, use a computer-readable and computer actionable license.</p>"));
}),
_122/* formItems1393 */ = new T1(1,_121/* Questionnaire.formItems1394 */),
_123/* formItems1396 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do all datasets you work with have a license?"));
}),
_124/* formItems1395 */ = new T1(1,_123/* Questionnaire.formItems1396 */),
_125/* formItems1392 */ = {_:0,a:_124/* Questionnaire.formItems1395 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_122/* Questionnaire.formItems1393 */,g:_XM/* Questionnaire.formItems70 */,h:_11U/* Questionnaire.formItems1390 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_126/* formItems1371 */ = new T2(5,_125/* Questionnaire.formItems1392 */,_120/* Questionnaire.formItems1372 */),
_127/* formItems1370 */ = new T2(1,_126/* Questionnaire.formItems1371 */,_k/* GHC.Types.[] */),
_128/* formItems1369 */ = new T3(8,_11V/* Questionnaire.formItems1389 */,_Q0/* Questionnaire.formItems31 */,_127/* Questionnaire.formItems1370 */),
_129/* formItems1291 */ = new T2(1,_128/* Questionnaire.formItems1369 */,_11G/* Questionnaire.formItems1292 */),
_12a/* formItems1414 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you define a way to detect file or sample swaps, e.g. by measuring something independently?"));
}),
_12b/* formItems1413 */ = new T1(1,_12a/* Questionnaire.formItems1414 */),
_12c/* formItems1410 */ = {_:0,a:_12b/* Questionnaire.formItems1413 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Th/* Questionnaire.formItems1411 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_12d/* formItems1409 */ = new T2(5,_12c/* Questionnaire.formItems1410 */,_PW/* Questionnaire.formItems18 */),
_12e/* formItems1408 */ = new T2(1,_12d/* Questionnaire.formItems1409 */,_k/* GHC.Types.[] */),
_12f/* formItems1415 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Th/* Questionnaire.formItems1411 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_12g/* formItems1407 */ = new T3(8,_12f/* Questionnaire.formItems1415 */,_Q0/* Questionnaire.formItems31 */,_12e/* Questionnaire.formItems1408 */),
_12h/* formItems1406 */ = new T2(1,_12g/* Questionnaire.formItems1407 */,_k/* GHC.Types.[] */),
_12i/* formItems1423 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Data corruption or mistakes can happen with large amounts of files or large files. Keeping a master list with data checksums can be helpful to prevent expensive mistakes. It can also be helpful to keep the sample list under version control forcing that all changes are well documented.</p>"));
}),
_12j/* formItems1422 */ = new T1(1,_12i/* Questionnaire.formItems1423 */),
_12k/* formItems1425 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be keeping a master list with checksums of certified/correct/canonical/verified data?"));
}),
_12l/* formItems1424 */ = new T1(1,_12k/* Questionnaire.formItems1425 */),
_12m/* formItems1419 */ = {_:0,a:_12l/* Questionnaire.formItems1424 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_12j/* Questionnaire.formItems1422 */,g:_XM/* Questionnaire.formItems70 */,h:_Tz/* Questionnaire.formItems1420 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_12n/* formItems1418 */ = new T2(5,_12m/* Questionnaire.formItems1419 */,_PW/* Questionnaire.formItems18 */),
_12o/* formItems1417 */ = new T2(1,_12n/* Questionnaire.formItems1418 */,_k/* GHC.Types.[] */),
_12p/* formItems1426 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Tz/* Questionnaire.formItems1420 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_12q/* formItems1416 */ = new T3(8,_12p/* Questionnaire.formItems1426 */,_Q0/* Questionnaire.formItems31 */,_12o/* Questionnaire.formItems1417 */),
_12r/* formItems1405 */ = new T2(1,_12q/* Questionnaire.formItems1416 */,_12h/* Questionnaire.formItems1406 */),
_12s/* formItems1427 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Rl/* Questionnaire.formItems1428 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_12t/* formItems1404 */ = new T3(8,_12s/* Questionnaire.formItems1427 */,_Q0/* Questionnaire.formItems31 */,_12r/* Questionnaire.formItems1405 */),
_12u/* formItems1403 */ = new T2(1,_12t/* Questionnaire.formItems1404 */,_k/* GHC.Types.[] */),
_12v/* formItems1402 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_11a/* Questionnaire.formItems432 */,_12u/* Questionnaire.formItems1403 */),
_12w/* formItems1401 */ = new T2(1,_12v/* Questionnaire.formItems1402 */,_k/* GHC.Types.[] */),
_12x/* formItems1400 */ = new T2(1,_11e/* Questionnaire.formItems40 */,_12w/* Questionnaire.formItems1401 */),
_12y/* formItems1432 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Working with large amounts of heterogenous data in a larger research group has implications for the data integrity. How do you make sure every step of the workflow is done with the right version of the data? How do you handle the situation when a mistake is uncovered? Will you be able to redo the strict minimum data handling?</p>"));
}),
_12z/* formItems1431 */ = new T1(1,_12y/* Questionnaire.formItems1432 */),
_12A/* formItems1434 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Did you consider how to monitor data integrity?"));
}),
_12B/* formItems1433 */ = new T1(1,_12A/* Questionnaire.formItems1434 */),
_12C/* formItems1430 */ = {_:0,a:_12B/* Questionnaire.formItems1433 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_12z/* Questionnaire.formItems1431 */,g:_XM/* Questionnaire.formItems70 */,h:_Rl/* Questionnaire.formItems1428 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_12D/* formItems1399 */ = new T2(5,_12C/* Questionnaire.formItems1430 */,_12x/* Questionnaire.formItems1400 */),
_12E/* formItems1398 */ = new T2(1,_12D/* Questionnaire.formItems1399 */,_k/* GHC.Types.[] */),
_12F/* formItems1397 */ = new T3(8,_12s/* Questionnaire.formItems1427 */,_Q0/* Questionnaire.formItems31 */,_12E/* Questionnaire.formItems1398 */),
_12G/* formItems1290 */ = new T2(1,_12F/* Questionnaire.formItems1397 */,_129/* Questionnaire.formItems1291 */),
_12H/* formItems1452 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you need to exchange your data with others?"));
}),
_12I/* formItems1451 */ = new T1(1,_12H/* Questionnaire.formItems1452 */),
_12J/* formItems1448 */ = {_:0,a:_12I/* Questionnaire.formItems1451 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_TR/* Questionnaire.formItems1449 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_12K/* formItems1447 */ = new T2(5,_12J/* Questionnaire.formItems1448 */,_PW/* Questionnaire.formItems18 */),
_12L/* formItems1446 */ = new T2(1,_12K/* Questionnaire.formItems1447 */,_k/* GHC.Types.[] */),
_12M/* formItems1453 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_TR/* Questionnaire.formItems1449 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_12N/* formItems1445 */ = new T3(8,_12M/* Questionnaire.formItems1453 */,_Q0/* Questionnaire.formItems31 */,_12L/* Questionnaire.formItems1446 */),
_12O/* formItems1444 */ = new T2(1,_12N/* Questionnaire.formItems1445 */,_k/* GHC.Types.[] */),
_12P/* formItems1461 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("I will store all metadata I can gather and document"));
}),
_12Q/* formItems1460 */ = new T1(0,_12P/* Questionnaire.formItems1461 */),
_12R/* formItems1459 */ = new T2(1,_12Q/* Questionnaire.formItems1460 */,_k/* GHC.Types.[] */),
_12S/* formItems1463 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("I will use preselected additional standard modules of metadata"));
}),
_12T/* formItems1462 */ = new T1(0,_12S/* Questionnaire.formItems1463 */),
_12U/* formItems1458 */ = new T2(1,_12T/* Questionnaire.formItems1462 */,_12R/* Questionnaire.formItems1459 */),
_12V/* formItems1465 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("I will see what I can do"));
}),
_12W/* formItems1464 */ = new T1(0,_12V/* Questionnaire.formItems1465 */),
_12X/* formItems1457 */ = new T2(1,_12W/* Questionnaire.formItems1464 */,_12U/* Questionnaire.formItems1458 */),
_12Y/* formItems1470 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you balance the extra efforts with the potential for added reusability?"));
}),
_12Z/* formItems1469 */ = new T1(1,_12Y/* Questionnaire.formItems1470 */),
_130/* formItems1466 */ = {_:0,a:_12Z/* Questionnaire.formItems1469 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Uc/* Questionnaire.formItems1467 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_131/* formItems1456 */ = new T2(5,_130/* Questionnaire.formItems1466 */,_12X/* Questionnaire.formItems1457 */),
_132/* formItems1455 */ = new T2(1,_131/* Questionnaire.formItems1456 */,_k/* GHC.Types.[] */),
_133/* formItems1471 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Uc/* Questionnaire.formItems1467 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_134/* formItems1454 */ = new T3(8,_133/* Questionnaire.formItems1471 */,_Q0/* Questionnaire.formItems31 */,_132/* Questionnaire.formItems1455 */),
_135/* formItems1443 */ = new T2(1,_134/* Questionnaire.formItems1454 */,_12O/* Questionnaire.formItems1444 */),
_136/* formItems1472 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Um/* Questionnaire.formItems1473 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_137/* formItems1442 */ = new T3(8,_136/* Questionnaire.formItems1472 */,_Q0/* Questionnaire.formItems31 */,_135/* Questionnaire.formItems1443 */),
_138/* formItems1441 */ = new T2(1,_137/* Questionnaire.formItems1442 */,_k/* GHC.Types.[] */),
_139/* formItems1475 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes, I will document more metadata than needed for reproducibility"));
}),
_13a/* formItems1440 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_139/* Questionnaire.formItems1475 */,_138/* Questionnaire.formItems1441 */),
_13b/* formItems1439 */ = new T2(1,_13a/* Questionnaire.formItems1440 */,_k/* GHC.Types.[] */),
_13c/* formItems1477 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No, I will just document the bare minimum"));
}),
_13d/* formItems1476 */ = new T1(0,_13c/* Questionnaire.formItems1477 */),
_13e/* formItems1438 */ = new T2(1,_13d/* Questionnaire.formItems1476 */,_13b/* Questionnaire.formItems1439 */),
_13f/* formItems1480 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Adding more than the strict minimum metadata about your experiment will possibly allow more wide re-use of your data, with associated higher data citation rates. Please note that it is not easy for yourself to see all other ways in which others could be reusing your data.</p>"));
}),
_13g/* formItems1479 */ = new T1(1,_13f/* Questionnaire.formItems1480 */),
_13h/* formItems1482 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you consider re-usability of your data beyond your original purpose?"));
}),
_13i/* formItems1481 */ = new T1(1,_13h/* Questionnaire.formItems1482 */),
_13j/* formItems1478 */ = {_:0,a:_13i/* Questionnaire.formItems1481 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_13g/* Questionnaire.formItems1479 */,g:_XM/* Questionnaire.formItems70 */,h:_Um/* Questionnaire.formItems1473 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_13k/* formItems1437 */ = new T2(5,_13j/* Questionnaire.formItems1478 */,_13e/* Questionnaire.formItems1438 */),
_13l/* formItems1436 */ = new T2(1,_13k/* Questionnaire.formItems1437 */,_k/* GHC.Types.[] */),
_13m/* formItems1435 */ = new T3(8,_136/* Questionnaire.formItems1472 */,_Q0/* Questionnaire.formItems31 */,_13l/* Questionnaire.formItems1436 */),
_13n/* formItems1289 */ = new T2(1,_13m/* Questionnaire.formItems1435 */,_12G/* Questionnaire.formItems1290 */),
_13o/* formItems1490 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do suitable \'Minimal Metadata About ...\' (MIA...) standards exist for your experiments?"));
}),
_13p/* formItems1489 */ = new T1(1,_13o/* Questionnaire.formItems1490 */),
_13q/* formItems1486 */ = {_:0,a:_13p/* Questionnaire.formItems1489 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_UF/* Questionnaire.formItems1487 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_13r/* formItems1485 */ = new T2(5,_13q/* Questionnaire.formItems1486 */,_PW/* Questionnaire.formItems18 */),
_13s/* formItems1484 */ = new T2(1,_13r/* Questionnaire.formItems1485 */,_k/* GHC.Types.[] */),
_13t/* formItems1491 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_UF/* Questionnaire.formItems1487 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_13u/* formItems1483 */ = new T3(8,_13t/* Questionnaire.formItems1491 */,_Q0/* Questionnaire.formItems31 */,_13s/* Questionnaire.formItems1484 */),
_13v/* formItems1288 */ = new T2(1,_13u/* Questionnaire.formItems1483 */,_13n/* Questionnaire.formItems1289 */),
_13w/* formItems1492 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Xz/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_13x/* formItems1287 */ = new T3(8,_13w/* Questionnaire.formItems1492 */,_Q0/* Questionnaire.formItems31 */,_13v/* Questionnaire.formItems1288 */),
_13y/* formItems1286 */ = new T2(1,_13x/* Questionnaire.formItems1287 */,_k/* GHC.Types.[] */),
_13z/* formItems1285 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_11a/* Questionnaire.formItems432 */,_13y/* Questionnaire.formItems1286 */),
_13A/* formItems1284 */ = new T2(1,_13z/* Questionnaire.formItems1285 */,_k/* GHC.Types.[] */),
_13B/* formItems1283 */ = new T2(1,_11e/* Questionnaire.formItems40 */,_13A/* Questionnaire.formItems1284 */),
_13C/* formItems1495 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">For the re-usability of your data by yourself or others at a later stage, a lot of information about the data, how it was collected and how it can be used should be stored with the data. Such data about the data is called metadata, and this set of questions are about this metadata</p>"));
}),
_13D/* formItems1494 */ = new T1(1,_13C/* Questionnaire.formItems1495 */),
_13E/* formItems1497 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you be storing metadata?"));
}),
_13F/* formItems1496 */ = new T1(1,_13E/* Questionnaire.formItems1497 */),
_13G/* formItems1493 */ = {_:0,a:_13F/* Questionnaire.formItems1496 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_13D/* Questionnaire.formItems1494 */,g:_XM/* Questionnaire.formItems70 */,h:_Xz/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_13H/* formItems1282 */ = new T2(5,_13G/* Questionnaire.formItems1493 */,_13B/* Questionnaire.formItems1283 */),
_13I/* formItems1281 */ = new T2(1,_13H/* Questionnaire.formItems1282 */,_k/* GHC.Types.[] */),
_13J/* formItems1280 */ = new T3(8,_13w/* Questionnaire.formItems1492 */,_Q0/* Questionnaire.formItems31 */,_13I/* Questionnaire.formItems1281 */),
_13K/* formItems1161 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("The risk is acceptably low"));
}),
_13L/* formItems1160 */ = new T1(0,_13K/* Questionnaire.formItems1161 */),
_13M/* formItems1159 */ = new T2(1,_13L/* Questionnaire.formItems1160 */,_k/* GHC.Types.[] */),
_13N/* formItems1163 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("The effect is small"));
}),
_13O/* formItems1162 */ = new T1(0,_13N/* Questionnaire.formItems1163 */),
_13P/* formItems1158 */ = new T2(1,_13O/* Questionnaire.formItems1162 */,_13M/* Questionnaire.formItems1159 */),
_13Q/* formItems1157 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_13P/* Questionnaire.formItems1158 */),
_13R/* formItems1166 */ = 84,
_13S/* formItems1165 */ = new T1(1,_13R/* Questionnaire.formItems1166 */),
_13T/* formItems1168 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Did you consider the possible impact to the project or organization if information is vandalized?"));
}),
_13U/* formItems1167 */ = new T1(1,_13T/* Questionnaire.formItems1168 */),
_13V/* formItems1164 */ = {_:0,a:_13U/* Questionnaire.formItems1167 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_13S/* Questionnaire.formItems1165 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_13W/* formItems1156 */ = new T2(5,_13V/* Questionnaire.formItems1164 */,_13Q/* Questionnaire.formItems1157 */),
_13X/* formItems1155 */ = new T2(1,_13W/* Questionnaire.formItems1156 */,_k/* GHC.Types.[] */),
_13Y/* formItems1169 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_13S/* Questionnaire.formItems1165 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_13Z/* formItems1154 */ = new T3(8,_13Y/* Questionnaire.formItems1169 */,_Q0/* Questionnaire.formItems31 */,_13X/* Questionnaire.formItems1155 */),
_140/* formItems1153 */ = new T2(1,_13Z/* Questionnaire.formItems1154 */,_k/* GHC.Types.[] */),
_141/* formItems1175 */ = 83,
_142/* formItems1174 */ = new T1(1,_141/* Questionnaire.formItems1175 */),
_143/* formItems1177 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Did you consider the possible impact to the project or organization if information leaks?"));
}),
_144/* formItems1176 */ = new T1(1,_143/* Questionnaire.formItems1177 */),
_145/* formItems1173 */ = {_:0,a:_144/* Questionnaire.formItems1176 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_142/* Questionnaire.formItems1174 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_146/* formItems1172 */ = new T2(5,_145/* Questionnaire.formItems1173 */,_13Q/* Questionnaire.formItems1157 */),
_147/* formItems1171 */ = new T2(1,_146/* Questionnaire.formItems1172 */,_k/* GHC.Types.[] */),
_148/* formItems1178 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_142/* Questionnaire.formItems1174 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_149/* formItems1170 */ = new T3(8,_148/* Questionnaire.formItems1178 */,_Q0/* Questionnaire.formItems31 */,_147/* Questionnaire.formItems1171 */),
_14a/* formItems1152 */ = new T2(1,_149/* Questionnaire.formItems1170 */,_140/* Questionnaire.formItems1153 */),
_14b/* formItems1184 */ = 82,
_14c/* formItems1183 */ = new T1(1,_14b/* Questionnaire.formItems1184 */),
_14d/* formItems1186 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Did you consider the possible impact to the project or organization if information is lost?"));
}),
_14e/* formItems1185 */ = new T1(1,_14d/* Questionnaire.formItems1186 */),
_14f/* formItems1182 */ = {_:0,a:_14e/* Questionnaire.formItems1185 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_14c/* Questionnaire.formItems1183 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_14g/* formItems1181 */ = new T2(5,_14f/* Questionnaire.formItems1182 */,_13Q/* Questionnaire.formItems1157 */),
_14h/* formItems1180 */ = new T2(1,_14g/* Questionnaire.formItems1181 */,_k/* GHC.Types.[] */),
_14i/* formItems1187 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_14c/* Questionnaire.formItems1183 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_14j/* formItems1179 */ = new T3(8,_14i/* Questionnaire.formItems1187 */,_Q0/* Questionnaire.formItems31 */,_14h/* Questionnaire.formItems1180 */),
_14k/* formItems1151 */ = new T2(1,_14j/* Questionnaire.formItems1179 */,_14a/* Questionnaire.formItems1152 */),
_14l/* formItems1195 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Project members may need to know about passwords (not sharing accounts, using different passwords for each service, and two factor authentication), about security for data they carry (encryption, backups), data stored in their own labs and in personal cloud accounts, and about the use of open WiFi and https</p>"));
}),
_14m/* formItems1194 */ = new T1(1,_14l/* Questionnaire.formItems1195 */),
_14n/* formItems1197 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Have project members been instructed about the risks (generic and specific to the project)?"));
}),
_14o/* formItems1196 */ = new T1(1,_14n/* Questionnaire.formItems1197 */),
_14p/* formItems1191 */ = {_:0,a:_14o/* Questionnaire.formItems1196 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_14m/* Questionnaire.formItems1194 */,g:_XM/* Questionnaire.formItems70 */,h:_R9/* Questionnaire.formItems1192 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_14q/* formItems1190 */ = new T2(5,_14p/* Questionnaire.formItems1191 */,_PW/* Questionnaire.formItems18 */),
_14r/* formItems1189 */ = new T2(1,_14q/* Questionnaire.formItems1190 */,_k/* GHC.Types.[] */),
_14s/* formItems1198 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_R9/* Questionnaire.formItems1192 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_14t/* formItems1188 */ = new T3(8,_14s/* Questionnaire.formItems1198 */,_Q0/* Questionnaire.formItems31 */,_14r/* Questionnaire.formItems1189 */),
_14u/* formItems1150 */ = new T2(1,_14t/* Questionnaire.formItems1188 */,_14k/* Questionnaire.formItems1151 */),
_14v/* formItems1206 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Are all project web services addressed via secure http (https://)?"));
}),
_14w/* formItems1205 */ = new T1(1,_14v/* Questionnaire.formItems1206 */),
_14x/* formItems1202 */ = {_:0,a:_14w/* Questionnaire.formItems1205 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_VI/* Questionnaire.formItems1203 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_14y/* formItems1201 */ = new T2(5,_14x/* Questionnaire.formItems1202 */,_PW/* Questionnaire.formItems18 */),
_14z/* formItems1200 */ = new T2(1,_14y/* Questionnaire.formItems1201 */,_k/* GHC.Types.[] */),
_14A/* formItems1207 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_VI/* Questionnaire.formItems1203 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_14B/* formItems1199 */ = new T3(8,_14A/* Questionnaire.formItems1207 */,_Q0/* Questionnaire.formItems31 */,_14z/* Questionnaire.formItems1200 */),
_14C/* formItems1149 */ = new T2(1,_14B/* Questionnaire.formItems1199 */,_14u/* Questionnaire.formItems1150 */),
_14D/* formItems1215 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do all data centers where project data is stored carry sufficient certifications?"));
}),
_14E/* formItems1214 */ = new T1(1,_14D/* Questionnaire.formItems1215 */),
_14F/* formItems1211 */ = {_:0,a:_14E/* Questionnaire.formItems1214 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_W6/* Questionnaire.formItems1212 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_14G/* formItems1210 */ = new T2(5,_14F/* Questionnaire.formItems1211 */,_PW/* Questionnaire.formItems18 */),
_14H/* formItems1209 */ = new T2(1,_14G/* Questionnaire.formItems1210 */,_k/* GHC.Types.[] */),
_14I/* formItems1216 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_W6/* Questionnaire.formItems1212 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_14J/* formItems1208 */ = new T3(8,_14I/* Questionnaire.formItems1216 */,_Q0/* Questionnaire.formItems31 */,_14H/* Questionnaire.formItems1209 */),
_14K/* formItems1148 */ = new T2(1,_14J/* Questionnaire.formItems1208 */,_14C/* Questionnaire.formItems1149 */),
_14L/* formItems1222 */ = 78,
_14M/* formItems1221 */ = new T1(1,_14L/* Questionnaire.formItems1222 */),
_14N/* formItems1224 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do project members send project data or reports per e-mail or other messaging services?"));
}),
_14O/* formItems1223 */ = new T1(1,_14N/* Questionnaire.formItems1224 */),
_14P/* formItems1220 */ = {_:0,a:_14O/* Questionnaire.formItems1223 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_14M/* Questionnaire.formItems1221 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_14Q/* formItems1219 */ = new T2(5,_14P/* Questionnaire.formItems1220 */,_PW/* Questionnaire.formItems18 */),
_14R/* formItems1218 */ = new T2(1,_14Q/* Questionnaire.formItems1219 */,_k/* GHC.Types.[] */),
_14S/* formItems1225 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_14M/* Questionnaire.formItems1221 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_14T/* formItems1217 */ = new T3(8,_14S/* Questionnaire.formItems1225 */,_Q0/* Questionnaire.formItems31 */,_14R/* Questionnaire.formItems1218 */),
_14U/* formItems1147 */ = new T2(1,_14T/* Questionnaire.formItems1217 */,_14K/* Questionnaire.formItems1148 */),
_14V/* formItems1231 */ = 77,
_14W/* formItems1230 */ = new T1(1,_14V/* Questionnaire.formItems1231 */),
_14X/* formItems1233 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Think about services like Dropbox, but also about Google Drive, Apple iCloud accounts, or Microsoft\'s Office365</p>"));
}),
_14Y/* formItems1232 */ = new T1(1,_14X/* Questionnaire.formItems1233 */),
_14Z/* formItems1235 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do project members store project data in cloud accounts?"));
}),
_150/* formItems1234 */ = new T1(1,_14Z/* Questionnaire.formItems1235 */),
_151/* formItems1229 */ = {_:0,a:_150/* Questionnaire.formItems1234 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_14Y/* Questionnaire.formItems1232 */,g:_XM/* Questionnaire.formItems70 */,h:_14W/* Questionnaire.formItems1230 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_152/* formItems1228 */ = new T2(5,_151/* Questionnaire.formItems1229 */,_PW/* Questionnaire.formItems18 */),
_153/* formItems1227 */ = new T2(1,_152/* Questionnaire.formItems1228 */,_k/* GHC.Types.[] */),
_154/* formItems1236 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_14W/* Questionnaire.formItems1230 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_155/* formItems1226 */ = new T3(8,_154/* Questionnaire.formItems1236 */,_Q0/* Questionnaire.formItems31 */,_153/* Questionnaire.formItems1227 */),
_156/* formItems1146 */ = new T2(1,_155/* Questionnaire.formItems1226 */,_14U/* Questionnaire.formItems1147 */),
_157/* formItems1251 */ = 76,
_158/* formItems1250 */ = new T1(1,_157/* Questionnaire.formItems1251 */),
_159/* formItems1253 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Are all data carriers encrypted? Are accounts on the laptop password protected?"));
}),
_15a/* formItems1252 */ = new T1(1,_159/* Questionnaire.formItems1253 */),
_15b/* formItems1249 */ = {_:0,a:_15a/* Questionnaire.formItems1252 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_158/* Questionnaire.formItems1250 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_15c/* formItems1248 */ = new T2(5,_15b/* Questionnaire.formItems1249 */,_PW/* Questionnaire.formItems18 */),
_15d/* formItems1247 */ = new T2(1,_15c/* Questionnaire.formItems1248 */,_k/* GHC.Types.[] */),
_15e/* formItems1254 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_158/* Questionnaire.formItems1250 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_15f/* formItems1246 */ = new T3(8,_15e/* Questionnaire.formItems1254 */,_Q0/* Questionnaire.formItems31 */,_15d/* Questionnaire.formItems1247 */),
_15g/* formItems1245 */ = new T2(1,_15f/* Questionnaire.formItems1246 */,_k/* GHC.Types.[] */),
_15h/* formItems1257 */ = 75,
_15i/* formItems1256 */ = new T1(1,_15h/* Questionnaire.formItems1257 */),
_15j/* formItems1255 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_15i/* Questionnaire.formItems1256 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_15k/* formItems1244 */ = new T3(8,_15j/* Questionnaire.formItems1255 */,_Q0/* Questionnaire.formItems31 */,_15g/* Questionnaire.formItems1245 */),
_15l/* formItems1243 */ = new T2(1,_15k/* Questionnaire.formItems1244 */,_k/* GHC.Types.[] */),
_15m/* formItems1242 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_15l/* Questionnaire.formItems1243 */),
_15n/* formItems1241 */ = new T2(1,_15m/* Questionnaire.formItems1242 */,_k/* GHC.Types.[] */),
_15o/* formItems1240 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_15n/* Questionnaire.formItems1241 */),
_15p/* formItems1260 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Does anyone carry project data on laptops, USB sticks or other external media?</p>"));
}),
_15q/* formItems1259 */ = new T1(1,_15p/* Questionnaire.formItems1260 */),
_15r/* formItems1262 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do project members carry data with them?"));
}),
_15s/* formItems1261 */ = new T1(1,_15r/* Questionnaire.formItems1262 */),
_15t/* formItems1258 */ = {_:0,a:_15s/* Questionnaire.formItems1261 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_15q/* Questionnaire.formItems1259 */,g:_XM/* Questionnaire.formItems70 */,h:_15i/* Questionnaire.formItems1256 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_15u/* formItems1239 */ = new T2(5,_15t/* Questionnaire.formItems1258 */,_15o/* Questionnaire.formItems1240 */),
_15v/* formItems1238 */ = new T2(1,_15u/* Questionnaire.formItems1239 */,_k/* GHC.Types.[] */),
_15w/* formItems1237 */ = new T3(8,_15j/* Questionnaire.formItems1255 */,_Q0/* Questionnaire.formItems31 */,_15v/* Questionnaire.formItems1238 */),
_15x/* formItems1145 */ = new T2(1,_15w/* Questionnaire.formItems1237 */,_156/* Questionnaire.formItems1146 */),
_15y/* formItems1268 */ = 74,
_15z/* formItems1267 */ = new T1(1,_15y/* Questionnaire.formItems1268 */),
_15A/* formItems1270 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">When assessing the risk, take into account who has access to the lab, who has (physical) access to the computer hardware itself. Also consider whether data on those systems is properly backed up</p>"));
}),
_15B/* formItems1269 */ = new T1(1,_15A/* Questionnaire.formItems1270 */),
_15C/* formItems1272 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do project members store data or software on computers in the lab or external hard drives connected to those computers?"));
}),
_15D/* formItems1271 */ = new T1(1,_15C/* Questionnaire.formItems1272 */),
_15E/* formItems1266 */ = {_:0,a:_15D/* Questionnaire.formItems1271 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_15B/* Questionnaire.formItems1269 */,g:_XM/* Questionnaire.formItems70 */,h:_15z/* Questionnaire.formItems1267 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_15F/* formItems1265 */ = new T2(5,_15E/* Questionnaire.formItems1266 */,_PW/* Questionnaire.formItems18 */),
_15G/* formItems1264 */ = new T2(1,_15F/* Questionnaire.formItems1265 */,_k/* GHC.Types.[] */),
_15H/* formItems1273 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_15z/* Questionnaire.formItems1267 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_15I/* formItems1263 */ = new T3(8,_15H/* Questionnaire.formItems1273 */,_Q0/* Questionnaire.formItems31 */,_15G/* Questionnaire.formItems1264 */),
_15J/* formItems1144 */ = new T2(1,_15I/* Questionnaire.formItems1263 */,_15x/* Questionnaire.formItems1145 */),
_15K/* formItems1274 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_X6/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_15L/* formItems1143 */ = new T3(8,_15K/* Questionnaire.formItems1274 */,_Q0/* Questionnaire.formItems31 */,_15J/* Questionnaire.formItems1144 */),
_15M/* formItems1142 */ = new T2(1,_15L/* Questionnaire.formItems1143 */,_k/* GHC.Types.[] */),
_15N/* formItems1141 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_11a/* Questionnaire.formItems432 */,_15M/* Questionnaire.formItems1142 */),
_15O/* formItems1140 */ = new T2(1,_15N/* Questionnaire.formItems1141 */,_k/* GHC.Types.[] */),
_15P/* formItems1139 */ = new T2(1,_11e/* Questionnaire.formItems40 */,_15O/* Questionnaire.formItems1140 */),
_15Q/* formItems1277 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">There are many factors that can contribute to the risk of information loss or information leaks. They are often part of the behavior of the people that are involved in the project, but can also be steered by properly planned infrastructure.</p>"));
}),
_15R/* formItems1276 */ = new T1(1,_15Q/* Questionnaire.formItems1277 */),
_15S/* formItems1279 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is the risk of information loss, leaks and vandalism acceptably low?"));
}),
_15T/* formItems1278 */ = new T1(1,_15S/* Questionnaire.formItems1279 */),
_15U/* formItems1275 */ = {_:0,a:_15T/* Questionnaire.formItems1278 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_15R/* Questionnaire.formItems1276 */,g:_XM/* Questionnaire.formItems70 */,h:_X6/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_15V/* formItems1138 */ = new T2(5,_15U/* Questionnaire.formItems1275 */,_15P/* Questionnaire.formItems1139 */),
_15W/* formItems1137 */ = new T2(1,_15V/* Questionnaire.formItems1138 */,_k/* GHC.Types.[] */),
_15X/* formItems1136 */ = new T3(8,_15K/* Questionnaire.formItems1274 */,_Q0/* Questionnaire.formItems31 */,_15W/* Questionnaire.formItems1137 */),
_15Y/* formItems1057 */ = 90,
_15Z/* formItems1056 */ = new T1(1,_15Y/* Questionnaire.formItems1057 */),
_160/* formItems1059 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Are the risks of data leaks covered?</p>"));
}),
_161/* formItems1058 */ = new T1(1,_160/* Questionnaire.formItems1059 */),
_162/* formItems1061 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Can all data be legally transported and processed at the computing site?"));
}),
_163/* formItems1060 */ = new T1(1,_162/* Questionnaire.formItems1061 */),
_164/* formItems1055 */ = {_:0,a:_163/* Questionnaire.formItems1060 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_161/* Questionnaire.formItems1058 */,g:_XM/* Questionnaire.formItems70 */,h:_15Z/* Questionnaire.formItems1056 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_165/* formItems1054 */ = new T2(5,_164/* Questionnaire.formItems1055 */,_PW/* Questionnaire.formItems18 */),
_166/* formItems1053 */ = new T2(1,_165/* Questionnaire.formItems1054 */,_k/* GHC.Types.[] */),
_167/* formItems1062 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_15Z/* Questionnaire.formItems1056 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_168/* formItems1052 */ = new T3(8,_167/* Questionnaire.formItems1062 */,_Q0/* Questionnaire.formItems31 */,_166/* Questionnaire.formItems1053 */),
_169/* formItems1051 */ = new T2(1,_168/* Questionnaire.formItems1052 */,_k/* GHC.Types.[] */),
_16a/* formItems1070 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We will be able to use a dedicated network connection"));
}),
_16b/* formItems1069 */ = new T1(0,_16a/* Questionnaire.formItems1070 */),
_16c/* formItems1068 */ = new T2(1,_16b/* Questionnaire.formItems1069 */,_k/* GHC.Types.[] */),
_16d/* formItems1072 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Copying or network delays are considered to be acceptable"));
}),
_16e/* formItems1071 */ = new T1(0,_16d/* Questionnaire.formItems1072 */),
_16f/* formItems1067 */ = new T2(1,_16e/* Questionnaire.formItems1071 */,_16c/* Questionnaire.formItems1068 */),
_16g/* formItems1074 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("There are no special networking requirements"));
}),
_16h/* formItems1073 */ = new T1(0,_16g/* Questionnaire.formItems1074 */),
_16i/* formItems1066 */ = new T2(1,_16h/* Questionnaire.formItems1073 */,_16f/* Questionnaire.formItems1067 */),
_16j/* formItems1077 */ = 89,
_16k/* formItems1076 */ = new T1(1,_16j/* Questionnaire.formItems1077 */),
_16l/* formItems1079 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Did you plan the required network capacity between storage and compute services?"));
}),
_16m/* formItems1078 */ = new T1(1,_16l/* Questionnaire.formItems1079 */),
_16n/* formItems1075 */ = {_:0,a:_16m/* Questionnaire.formItems1078 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_16k/* Questionnaire.formItems1076 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_16o/* formItems1065 */ = new T2(5,_16n/* Questionnaire.formItems1075 */,_16i/* Questionnaire.formItems1066 */),
_16p/* formItems1064 */ = new T2(1,_16o/* Questionnaire.formItems1065 */,_k/* GHC.Types.[] */),
_16q/* formItems1080 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_16k/* Questionnaire.formItems1076 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_16r/* formItems1063 */ = new T3(8,_16q/* Questionnaire.formItems1080 */,_Q0/* Questionnaire.formItems31 */,_16p/* Questionnaire.formItems1064 */),
_16s/* formItems1050 */ = new T2(1,_16r/* Questionnaire.formItems1063 */,_169/* Questionnaire.formItems1051 */),
_16t/* formItems1083 */ = 88,
_16u/* formItems1082 */ = new T1(1,_16t/* Questionnaire.formItems1083 */),
_16v/* formItems1081 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_16u/* Questionnaire.formItems1082 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_16w/* formItems1049 */ = new T3(8,_16v/* Questionnaire.formItems1081 */,_Q0/* Questionnaire.formItems31 */,_16s/* Questionnaire.formItems1050 */),
_16x/* formItems1048 */ = new T2(1,_16w/* Questionnaire.formItems1049 */,_k/* GHC.Types.[] */),
_16y/* formItems1047 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PU/* Questionnaire.formItems23 */,_16x/* Questionnaire.formItems1048 */),
_16z/* formItems1046 */ = new T2(1,_16y/* Questionnaire.formItems1047 */,_PT/* Questionnaire.formItems19 */),
_16A/* formItems1086 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is all required compute capacity available close to the project working storage area?"));
}),
_16B/* formItems1085 */ = new T1(1,_16A/* Questionnaire.formItems1086 */),
_16C/* formItems1084 */ = {_:0,a:_16B/* Questionnaire.formItems1085 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_16u/* Questionnaire.formItems1082 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_16D/* formItems1045 */ = new T2(5,_16C/* Questionnaire.formItems1084 */,_16z/* Questionnaire.formItems1046 */),
_16E/* formItems1044 */ = new T2(1,_16D/* Questionnaire.formItems1045 */,_k/* GHC.Types.[] */),
_16F/* formItems1043 */ = new T3(8,_16v/* Questionnaire.formItems1081 */,_Q0/* Questionnaire.formItems31 */,_16E/* Questionnaire.formItems1044 */),
_16G/* formItems1042 */ = new T2(1,_16F/* Questionnaire.formItems1043 */,_k/* GHC.Types.[] */),
_16H/* formItems1092 */ = 87,
_16I/* formItems1091 */ = new T1(1,_16H/* Questionnaire.formItems1092 */),
_16J/* formItems1094 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Do you need the compute capacity also for development? Can you start developing locally and start with a deployment test later?</p>"));
}),
_16K/* formItems1093 */ = new T1(1,_16J/* Questionnaire.formItems1094 */),
_16L/* formItems1096 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Have you established with the provider when will you need the compute capacity?"));
}),
_16M/* formItems1095 */ = new T1(1,_16L/* Questionnaire.formItems1096 */),
_16N/* formItems1090 */ = {_:0,a:_16M/* Questionnaire.formItems1095 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_16K/* Questionnaire.formItems1093 */,g:_XM/* Questionnaire.formItems70 */,h:_16I/* Questionnaire.formItems1091 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_16O/* formItems1089 */ = new T2(5,_16N/* Questionnaire.formItems1090 */,_PW/* Questionnaire.formItems18 */),
_16P/* formItems1088 */ = new T2(1,_16O/* Questionnaire.formItems1089 */,_k/* GHC.Types.[] */),
_16Q/* formItems1097 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_16I/* Questionnaire.formItems1091 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_16R/* formItems1087 */ = new T3(8,_16Q/* Questionnaire.formItems1097 */,_Q0/* Questionnaire.formItems31 */,_16P/* Questionnaire.formItems1088 */),
_16S/* formItems1041 */ = new T2(1,_16R/* Questionnaire.formItems1087 */,_16G/* Questionnaire.formItems1042 */),
_16T/* formItems1106 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We will use a mix of computing architectures for different parts of the work"));
}),
_16U/* formItems1105 */ = new T1(0,_16T/* Questionnaire.formItems1106 */),
_16V/* formItems1104 */ = new T2(1,_16U/* Questionnaire.formItems1105 */,_k/* GHC.Types.[] */),
_16W/* formItems1108 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We will use cloud computing"));
}),
_16X/* formItems1107 */ = new T1(0,_16W/* Questionnaire.formItems1108 */),
_16Y/* formItems1103 */ = new T2(1,_16X/* Questionnaire.formItems1107 */,_16V/* Questionnaire.formItems1104 */),
_16Z/* formItems1110 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We will use grid computing"));
}),
_170/* formItems1109 */ = new T1(0,_16Z/* Questionnaire.formItems1110 */),
_171/* formItems1102 */ = new T2(1,_170/* Questionnaire.formItems1109 */,_16Y/* Questionnaire.formItems1103 */),
_172/* formItems1112 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We will use a compute cluster"));
}),
_173/* formItems1111 */ = new T1(0,_172/* Questionnaire.formItems1112 */),
_174/* formItems1101 */ = new T2(1,_173/* Questionnaire.formItems1111 */,_171/* Questionnaire.formItems1102 */),
_175/* formItems1115 */ = 86,
_176/* formItems1114 */ = new T1(1,_175/* Questionnaire.formItems1115 */),
_177/* formItems1117 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What type of compute architecture is most suitable for your work? Will you have that available?"));
}),
_178/* formItems1116 */ = new T1(1,_177/* Questionnaire.formItems1117 */),
_179/* formItems1113 */ = {_:0,a:_178/* Questionnaire.formItems1116 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_176/* Questionnaire.formItems1114 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_17a/* formItems1100 */ = new T2(5,_179/* Questionnaire.formItems1113 */,_174/* Questionnaire.formItems1101 */),
_17b/* formItems1099 */ = new T2(1,_17a/* Questionnaire.formItems1100 */,_k/* GHC.Types.[] */),
_17c/* formItems1118 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_176/* Questionnaire.formItems1114 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_17d/* formItems1098 */ = new T3(8,_17c/* Questionnaire.formItems1118 */,_Q0/* Questionnaire.formItems31 */,_17b/* Questionnaire.formItems1099 */),
_17e/* formItems1040 */ = new T2(1,_17d/* Questionnaire.formItems1098 */,_16S/* Questionnaire.formItems1041 */),
_17f/* formItems1124 */ = 85,
_17g/* formItems1123 */ = new T1(1,_17f/* Questionnaire.formItems1124 */),
_17h/* formItems1126 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Did you run pilot jobs? Do you know this information from comparable projects? Did you test whether the work scales up as you expected if you run more than one job?</p>"));
}),
_17i/* formItems1125 */ = new T1(1,_17h/* Questionnaire.formItems1126 */),
_17j/* formItems1128 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you know how much CPU power, memory and I/O band width a typical analysis will take?"));
}),
_17k/* formItems1127 */ = new T1(1,_17j/* Questionnaire.formItems1128 */),
_17l/* formItems1122 */ = {_:0,a:_17k/* Questionnaire.formItems1127 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_17i/* Questionnaire.formItems1125 */,g:_XM/* Questionnaire.formItems70 */,h:_17g/* Questionnaire.formItems1123 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_17m/* formItems1121 */ = new T2(5,_17l/* Questionnaire.formItems1122 */,_PW/* Questionnaire.formItems18 */),
_17n/* formItems1120 */ = new T2(1,_17m/* Questionnaire.formItems1121 */,_k/* GHC.Types.[] */),
_17o/* formItems1129 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_17g/* Questionnaire.formItems1123 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_17p/* formItems1119 */ = new T3(8,_17o/* Questionnaire.formItems1129 */,_Q0/* Questionnaire.formItems31 */,_17n/* Questionnaire.formItems1120 */),
_17q/* formItems1039 */ = new T2(1,_17p/* Questionnaire.formItems1119 */,_17e/* Questionnaire.formItems1040 */),
_17r/* formItems1130 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_WL/* Questionnaire.formItems25 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_17s/* formItems1038 */ = new T3(8,_17r/* Questionnaire.formItems1130 */,_Q0/* Questionnaire.formItems31 */,_17q/* Questionnaire.formItems1039 */),
_17t/* formItems1037 */ = new T2(1,_17s/* Questionnaire.formItems1038 */,_k/* GHC.Types.[] */),
_17u/* formItems1036 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_17t/* Questionnaire.formItems1037 */),
_17v/* formItems1035 */ = new T2(1,_17u/* Questionnaire.formItems1036 */,_k/* GHC.Types.[] */),
_17w/* formItems1034 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_17v/* Questionnaire.formItems1035 */),
_17x/* formItems1133 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">If you require substantial amounts of compute power, amounts that are not trivially absorbed in what you usually have abailable, some planning is necessary. Do you think you need to do compute capacity planning?</p>"));
}),
_17y/* formItems1132 */ = new T1(1,_17x/* Questionnaire.formItems1133 */),
_17z/* formItems1135 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you need to do compute capacity planning?"));
}),
_17A/* formItems1134 */ = new T1(1,_17z/* Questionnaire.formItems1135 */),
_17B/* formItems1131 */ = {_:0,a:_17A/* Questionnaire.formItems1134 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_17y/* Questionnaire.formItems1132 */,g:_XM/* Questionnaire.formItems70 */,h:_WL/* Questionnaire.formItems25 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_17C/* formItems1033 */ = new T2(5,_17B/* Questionnaire.formItems1131 */,_17w/* Questionnaire.formItems1034 */),
_17D/* formItems1032 */ = new T2(1,_17C/* Questionnaire.formItems1033 */,_k/* GHC.Types.[] */),
_17E/* formItems1031 */ = new T3(8,_17r/* Questionnaire.formItems1130 */,_Q0/* Questionnaire.formItems31 */,_17D/* Questionnaire.formItems1032 */),
_17F/* formItems326 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We make (automated) backups of all data stored outside of the working area"));
}),
_17G/* formItems325 */ = new T1(0,_17F/* Questionnaire.formItems326 */),
_17H/* formItems324 */ = new T2(1,_17G/* Questionnaire.formItems325 */,_k/* GHC.Types.[] */),
_17I/* formItems328 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("All data elsewhere is adequately backed up"));
}),
_17J/* formItems327 */ = new T1(0,_17I/* Questionnaire.formItems328 */),
_17K/* formItems323 */ = new T2(1,_17J/* Questionnaire.formItems327 */,_17H/* Questionnaire.formItems324 */),
_17L/* formItems330 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("There is no data elsewhere"));
}),
_17M/* formItems329 */ = new T1(0,_17L/* Questionnaire.formItems330 */),
_17N/* formItems322 */ = new T2(1,_17M/* Questionnaire.formItems329 */,_17K/* Questionnaire.formItems323 */),
_17O/* formItems333 */ = 72,
_17P/* formItems332 */ = new T1(1,_17O/* Questionnaire.formItems333 */),
_17Q/* formItems335 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Are there any data files e.g. on laptops of project members? Also: supercomputing centers and other high performance computer centers often write in their terms of use that you need to take care of your own backups</p>"));
}),
_17R/* formItems334 */ = new T1(1,_17Q/* Questionnaire.formItems335 */),
_17S/* formItems337 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you need to make backups of project data stored elsewhere into your work space?"));
}),
_17T/* formItems336 */ = new T1(1,_17S/* Questionnaire.formItems337 */),
_17U/* formItems331 */ = {_:0,a:_17T/* Questionnaire.formItems336 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_17R/* Questionnaire.formItems334 */,g:_XM/* Questionnaire.formItems70 */,h:_17P/* Questionnaire.formItems332 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_17V/* formItems321 */ = new T2(5,_17U/* Questionnaire.formItems331 */,_17N/* Questionnaire.formItems322 */),
_17W/* formItems320 */ = new T2(1,_17V/* Questionnaire.formItems321 */,_k/* GHC.Types.[] */),
_17X/* formItems338 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_17P/* Questionnaire.formItems332 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_17Y/* formItems319 */ = new T3(8,_17X/* Questionnaire.formItems338 */,_Q0/* Questionnaire.formItems31 */,_17W/* Questionnaire.formItems320 */),
_17Z/* formItems318 */ = new T2(1,_17Y/* Questionnaire.formItems319 */,_k/* GHC.Types.[] */),
_180/* formItems346 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Any user needs to be able to restore an old copy instantaneously"));
}),
_181/* formItems345 */ = new T1(0,_180/* Questionnaire.formItems346 */),
_182/* formItems344 */ = new T2(1,_181/* Questionnaire.formItems345 */,_k/* GHC.Types.[] */),
_183/* formItems348 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Hours"));
}),
_184/* formItems347 */ = new T1(0,_183/* Questionnaire.formItems348 */),
_185/* formItems343 */ = new T2(1,_184/* Questionnaire.formItems347 */,_182/* Questionnaire.formItems344 */),
_186/* formItems350 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Days"));
}),
_187/* formItems349 */ = new T1(0,_186/* Questionnaire.formItems350 */),
_188/* formItems342 */ = new T2(1,_187/* Questionnaire.formItems349 */,_185/* Questionnaire.formItems343 */),
_189/* formItems353 */ = 70,
_18a/* formItems352 */ = new T1(1,_189/* Questionnaire.formItems353 */),
_18b/* formItems355 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How long can you wait for a restore if you accidentally damage a file?"));
}),
_18c/* formItems354 */ = new T1(1,_18b/* Questionnaire.formItems355 */),
_18d/* formItems351 */ = {_:0,a:_18c/* Questionnaire.formItems354 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_18a/* Questionnaire.formItems352 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_18e/* formItems341 */ = new T2(5,_18d/* Questionnaire.formItems351 */,_188/* Questionnaire.formItems342 */),
_18f/* formItems340 */ = new T2(1,_18e/* Questionnaire.formItems341 */,_k/* GHC.Types.[] */),
_18g/* formItems356 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_18a/* Questionnaire.formItems352 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_18h/* formItems339 */ = new T3(8,_18g/* Questionnaire.formItems356 */,_Q0/* Questionnaire.formItems31 */,_18f/* Questionnaire.formItems340 */),
_18i/* formItems317 */ = new T2(1,_18h/* Questionnaire.formItems339 */,_17Z/* Questionnaire.formItems318 */),
_18j/* formItems364 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No waiting is possible, a hot copy must be ready to take over"));
}),
_18k/* formItems363 */ = new T1(0,_18j/* Questionnaire.formItems364 */),
_18l/* formItems362 */ = new T2(1,_18k/* Questionnaire.formItems363 */,_k/* GHC.Types.[] */),
_18m/* formItems366 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("A spare copy needs to be deployed quickly"));
}),
_18n/* formItems365 */ = new T1(0,_18m/* Questionnaire.formItems366 */),
_18o/* formItems361 */ = new T2(1,_18n/* Questionnaire.formItems365 */,_18l/* Questionnaire.formItems362 */),
_18p/* formItems368 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We can wait for repair and a restore from tape"));
}),
_18q/* formItems367 */ = new T1(0,_18p/* Questionnaire.formItems368 */),
_18r/* formItems360 */ = new T2(1,_18q/* Questionnaire.formItems367 */,_18o/* Questionnaire.formItems361 */),
_18s/* formItems371 */ = 69,
_18t/* formItems370 */ = new T1(1,_18s/* Questionnaire.formItems371 */),
_18u/* formItems373 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How long can you wait for a restore if the storage fails?"));
}),
_18v/* formItems372 */ = new T1(1,_18u/* Questionnaire.formItems373 */),
_18w/* formItems369 */ = {_:0,a:_18v/* Questionnaire.formItems372 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_18t/* Questionnaire.formItems370 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_18x/* formItems359 */ = new T2(5,_18w/* Questionnaire.formItems369 */,_18r/* Questionnaire.formItems360 */),
_18y/* formItems358 */ = new T2(1,_18x/* Questionnaire.formItems359 */,_k/* GHC.Types.[] */),
_18z/* formItems374 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_18t/* Questionnaire.formItems370 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_18A/* formItems357 */ = new T3(8,_18z/* Questionnaire.formItems374 */,_Q0/* Questionnaire.formItems31 */,_18y/* Questionnaire.formItems358 */),
_18B/* formItems316 */ = new T2(1,_18A/* Questionnaire.formItems357 */,_18i/* Questionnaire.formItems317 */),
_18C/* formItems382 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Problems during the evenings and weekends can not wait for work hours to be repaired"));
}),
_18D/* formItems381 */ = new T1(0,_18C/* Questionnaire.formItems382 */),
_18E/* formItems380 */ = new T2(1,_18D/* Questionnaire.formItems381 */,_k/* GHC.Types.[] */),
_18F/* formItems384 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We can only miss the work space for a few hours during work hours"));
}),
_18G/* formItems383 */ = new T1(0,_18F/* Questionnaire.formItems384 */),
_18H/* formItems379 */ = new T2(1,_18G/* Questionnaire.formItems383 */,_18E/* Questionnaire.formItems380 */),
_18I/* formItems386 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We could handle a few days of offline time per year"));
}),
_18J/* formItems385 */ = new T1(0,_18I/* Questionnaire.formItems386 */),
_18K/* formItems378 */ = new T2(1,_18J/* Questionnaire.formItems385 */,_18H/* Questionnaire.formItems379 */),
_18L/* formItems389 */ = 68,
_18M/* formItems388 */ = new T1(1,_18L/* Questionnaire.formItems389 */),
_18N/* formItems391 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Can you handle it when the work space is off line for a while?"));
}),
_18O/* formItems390 */ = new T1(1,_18N/* Questionnaire.formItems391 */),
_18P/* formItems387 */ = {_:0,a:_18O/* Questionnaire.formItems390 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_18M/* Questionnaire.formItems388 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_18Q/* formItems377 */ = new T2(5,_18P/* Questionnaire.formItems387 */,_18K/* Questionnaire.formItems378 */),
_18R/* formItems376 */ = new T2(1,_18Q/* Questionnaire.formItems377 */,_k/* GHC.Types.[] */),
_18S/* formItems392 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_18M/* Questionnaire.formItems388 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_18T/* formItems375 */ = new T3(8,_18S/* Questionnaire.formItems392 */,_Q0/* Questionnaire.formItems31 */,_18R/* Questionnaire.formItems376 */),
_18U/* formItems315 */ = new T2(1,_18T/* Questionnaire.formItems375 */,_18B/* Questionnaire.formItems316 */),
_18V/* formItems409 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Special care will be taken for the software and configurations"));
}),
_18W/* formItems408 */ = new T1(0,_18V/* Questionnaire.formItems409 */),
_18X/* formItems407 */ = new T2(1,_18W/* Questionnaire.formItems408 */,_k/* GHC.Types.[] */),
_18Y/* formItems411 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Software in the work space is only a copy"));
}),
_18Z/* formItems410 */ = new T1(0,_18Y/* Questionnaire.formItems411 */),
_190/* formItems406 */ = new T2(1,_18Z/* Questionnaire.formItems410 */,_18X/* Questionnaire.formItems407 */),
_191/* formItems413 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("There is no software"));
}),
_192/* formItems412 */ = new T1(0,_191/* Questionnaire.formItems413 */),
_193/* formItems405 */ = new T2(1,_192/* Questionnaire.formItems412 */,_190/* Questionnaire.formItems406 */),
_194/* formItems416 */ = 67,
_195/* formItems415 */ = new T1(1,_194/* Questionnaire.formItems416 */),
_196/* formItems418 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is there software in the work space? Can it also be restored quickly?"));
}),
_197/* formItems417 */ = new T1(1,_196/* Questionnaire.formItems418 */),
_198/* formItems414 */ = {_:0,a:_197/* Questionnaire.formItems417 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_195/* Questionnaire.formItems415 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_199/* formItems404 */ = new T2(5,_198/* Questionnaire.formItems414 */,_193/* Questionnaire.formItems405 */),
_19a/* formItems403 */ = new T2(1,_199/* Questionnaire.formItems404 */,_k/* GHC.Types.[] */),
_19b/* formItems419 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_195/* Questionnaire.formItems415 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_19c/* formItems402 */ = new T3(8,_19b/* Questionnaire.formItems419 */,_Q0/* Questionnaire.formItems31 */,_19a/* Questionnaire.formItems403 */),
_19d/* formItems401 */ = new T2(1,_19c/* Questionnaire.formItems402 */,_k/* GHC.Types.[] */),
_19e/* formItems422 */ = 66,
_19f/* formItems421 */ = new T1(1,_19e/* Questionnaire.formItems422 */),
_19g/* formItems420 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_19f/* Questionnaire.formItems421 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_19h/* formItems400 */ = new T3(8,_19g/* Questionnaire.formItems420 */,_Q0/* Questionnaire.formItems31 */,_19d/* Questionnaire.formItems401 */),
_19i/* formItems399 */ = new T2(1,_19h/* Questionnaire.formItems400 */,_k/* GHC.Types.[] */),
_19j/* formItems423 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("All essential data is also stored elsewhere"));
}),
_19k/* formItems398 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_19j/* Questionnaire.formItems423 */,_19i/* Questionnaire.formItems399 */),
_19l/* formItems397 */ = new T2(1,_19k/* Questionnaire.formItems398 */,_k/* GHC.Types.[] */),
_19m/* formItems425 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("This is unacceptable"));
}),
_19n/* formItems424 */ = new T1(0,_19m/* Questionnaire.formItems425 */),
_19o/* formItems396 */ = new T2(1,_19n/* Questionnaire.formItems424 */,_19l/* Questionnaire.formItems397 */),
_19p/* formItems428 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What is the acceptable risk for a total loss?"));
}),
_19q/* formItems427 */ = new T1(1,_19p/* Questionnaire.formItems428 */),
_19r/* formItems426 */ = {_:0,a:_19q/* Questionnaire.formItems427 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_19f/* Questionnaire.formItems421 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_19s/* formItems395 */ = new T2(5,_19r/* Questionnaire.formItems426 */,_19o/* Questionnaire.formItems396 */),
_19t/* formItems394 */ = new T2(1,_19s/* Questionnaire.formItems395 */,_k/* GHC.Types.[] */),
_19u/* formItems393 */ = new T3(8,_19g/* Questionnaire.formItems420 */,_Q0/* Questionnaire.formItems31 */,_19t/* Questionnaire.formItems394 */),
_19v/* formItems314 */ = new T2(1,_19u/* Questionnaire.formItems393 */,_18U/* Questionnaire.formItems315 */),
_19w/* formItems431 */ = 65,
_19x/* formItems430 */ = new T1(1,_19w/* Questionnaire.formItems431 */),
_19y/* formItems429 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_19x/* Questionnaire.formItems430 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_19z/* formItems313 */ = new T3(8,_19y/* Questionnaire.formItems429 */,_Q0/* Questionnaire.formItems31 */,_19v/* Questionnaire.formItems314 */),
_19A/* formItems312 */ = new T2(1,_19z/* Questionnaire.formItems313 */,_k/* GHC.Types.[] */),
_19B/* formItems311 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_11a/* Questionnaire.formItems432 */,_19A/* Questionnaire.formItems312 */),
_19C/* formItems310 */ = new T2(1,_19B/* Questionnaire.formItems311 */,_k/* GHC.Types.[] */),
_19D/* formItems309 */ = new T2(1,_11e/* Questionnaire.formItems40 */,_19C/* Questionnaire.formItems310 */),
_19E/* formItems435 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How available/reliable should must the workspace be?"));
}),
_19F/* formItems434 */ = new T1(1,_19E/* Questionnaire.formItems435 */),
_19G/* formItems433 */ = {_:0,a:_19F/* Questionnaire.formItems434 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_19x/* Questionnaire.formItems430 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_19H/* formItems308 */ = new T2(5,_19G/* Questionnaire.formItems433 */,_19D/* Questionnaire.formItems309 */),
_19I/* formItems307 */ = new T2(1,_19H/* Questionnaire.formItems308 */,_k/* GHC.Types.[] */),
_19J/* formItems306 */ = new T3(8,_19y/* Questionnaire.formItems429 */,_Q0/* Questionnaire.formItems31 */,_19I/* Questionnaire.formItems307 */),
_19K/* formItems305 */ = new T2(1,_19J/* Questionnaire.formItems306 */,_k/* GHC.Types.[] */),
_19L/* formItems477 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("This is not needed"));
}),
_19M/* formItems476 */ = new T1(0,_19L/* Questionnaire.formItems477 */),
_19N/* formItems475 */ = new T2(1,_19M/* Questionnaire.formItems476 */,_PT/* Questionnaire.formItems19 */),
_19O/* formItems480 */ = 64,
_19P/* formItems479 */ = new T1(1,_19O/* Questionnaire.formItems480 */),
_19Q/* formItems482 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Are data integrity and reliability requirements also met by the other storage spaces used in the project?"));
}),
_19R/* formItems481 */ = new T1(1,_19Q/* Questionnaire.formItems482 */),
_19S/* formItems478 */ = {_:0,a:_19R/* Questionnaire.formItems481 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_19P/* Questionnaire.formItems479 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_19T/* formItems474 */ = new T2(5,_19S/* Questionnaire.formItems478 */,_19N/* Questionnaire.formItems475 */),
_19U/* formItems473 */ = new T2(1,_19T/* Questionnaire.formItems474 */,_k/* GHC.Types.[] */),
_19V/* formItems483 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_19P/* Questionnaire.formItems479 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_19W/* formItems472 */ = new T3(8,_19V/* Questionnaire.formItems483 */,_Q0/* Questionnaire.formItems31 */,_19U/* Questionnaire.formItems473 */),
_19X/* formItems471 */ = new T2(1,_19W/* Questionnaire.formItems472 */,_k/* GHC.Types.[] */),
_19Y/* formItems486 */ = 63,
_19Z/* formItems485 */ = new T1(1,_19Y/* Questionnaire.formItems486 */),
_1a0/* formItems484 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_19Z/* Questionnaire.formItems485 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1a1/* formItems470 */ = new T3(8,_1a0/* Questionnaire.formItems484 */,_Q0/* Questionnaire.formItems31 */,_19X/* Questionnaire.formItems471 */),
_1a2/* formItems469 */ = new T2(1,_1a1/* Questionnaire.formItems470 */,_k/* GHC.Types.[] */),
_1a3/* formItems487 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes, for actual computations, requiring high performance"));
}),
_1a4/* formItems468 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_1a3/* Questionnaire.formItems487 */,_1a2/* Questionnaire.formItems469 */),
_1a5/* formItems467 */ = new T2(1,_1a4/* Questionnaire.formItems468 */,_k/* GHC.Types.[] */),
_1a6/* formItems489 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes, occasionally"));
}),
_1a7/* formItems488 */ = new T1(0,_1a6/* Questionnaire.formItems489 */),
_1a8/* formItems466 */ = new T2(1,_1a7/* Questionnaire.formItems488 */,_1a5/* Questionnaire.formItems467 */),
_1a9/* formItems491 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No, this should not be allowed"));
}),
_1aa/* formItems490 */ = new T1(0,_1a9/* Questionnaire.formItems491 */),
_1ab/* formItems465 */ = new T2(1,_1aa/* Questionnaire.formItems490 */,_1a8/* Questionnaire.formItems466 */),
_1ac/* formItems494 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will data be copied out and in to the workspace by remote users?"));
}),
_1ad/* formItems493 */ = new T1(1,_1ac/* Questionnaire.formItems494 */),
_1ae/* formItems492 */ = {_:0,a:_1ad/* Questionnaire.formItems493 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_19Z/* Questionnaire.formItems485 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1af/* formItems464 */ = new T2(5,_1ae/* Questionnaire.formItems492 */,_1ab/* Questionnaire.formItems465 */),
_1ag/* formItems463 */ = new T2(1,_1af/* Questionnaire.formItems464 */,_k/* GHC.Types.[] */),
_1ah/* formItems462 */ = new T3(8,_1a0/* Questionnaire.formItems484 */,_Q0/* Questionnaire.formItems31 */,_1ag/* Questionnaire.formItems463 */),
_1ai/* formItems461 */ = new T2(1,_1ah/* Questionnaire.formItems462 */,_k/* GHC.Types.[] */),
_1aj/* formItems501 */ = new T1(0,_1a3/* Questionnaire.formItems487 */),
_1ak/* formItems500 */ = new T2(1,_1aj/* Questionnaire.formItems501 */,_k/* GHC.Types.[] */),
_1al/* formItems503 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes, for occasional exploration"));
}),
_1am/* formItems502 */ = new T1(0,_1al/* Questionnaire.formItems503 */),
_1an/* formItems499 */ = new T2(1,_1am/* Questionnaire.formItems502 */,_1ak/* Questionnaire.formItems500 */),
_1ao/* formItems498 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_1an/* Questionnaire.formItems499 */),
_1ap/* formItems506 */ = 62,
_1aq/* formItems505 */ = new T1(1,_1ap/* Questionnaire.formItems506 */),
_1ar/* formItems508 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will the work space need to be remote mounted?"));
}),
_1as/* formItems507 */ = new T1(1,_1ar/* Questionnaire.formItems508 */),
_1at/* formItems504 */ = {_:0,a:_1as/* Questionnaire.formItems507 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1aq/* Questionnaire.formItems505 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1au/* formItems497 */ = new T2(5,_1at/* Questionnaire.formItems504 */,_1ao/* Questionnaire.formItems498 */),
_1av/* formItems496 */ = new T2(1,_1au/* Questionnaire.formItems497 */,_k/* GHC.Types.[] */),
_1aw/* formItems509 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1aq/* Questionnaire.formItems505 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1ax/* formItems495 */ = new T3(8,_1aw/* Questionnaire.formItems509 */,_Q0/* Questionnaire.formItems31 */,_1av/* Questionnaire.formItems496 */),
_1ay/* formItems460 */ = new T2(1,_1ax/* Questionnaire.formItems495 */,_1ai/* Questionnaire.formItems461 */),
_1az/* formItems517 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("The work space should be connected to a single-sign-on system"));
}),
_1aA/* formItems516 */ = new T1(0,_1az/* Questionnaire.formItems517 */),
_1aB/* formItems515 */ = new T2(1,_1aA/* Questionnaire.formItems516 */,_k/* GHC.Types.[] */),
_1aC/* formItems519 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Project management will need to be able to give people access"));
}),
_1aD/* formItems518 */ = new T1(0,_1aC/* Questionnaire.formItems519 */),
_1aE/* formItems514 */ = new T2(1,_1aD/* Questionnaire.formItems518 */,_1aB/* Questionnaire.formItems515 */),
_1aF/* formItems521 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No special provisions are needed"));
}),
_1aG/* formItems520 */ = new T1(0,_1aF/* Questionnaire.formItems521 */),
_1aH/* formItems513 */ = new T2(1,_1aG/* Questionnaire.formItems520 */,_1aE/* Questionnaire.formItems514 */),
_1aI/* formItems524 */ = 61,
_1aJ/* formItems523 */ = new T1(1,_1aI/* Questionnaire.formItems524 */),
_1aK/* formItems526 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Who will arrange access control?"));
}),
_1aL/* formItems525 */ = new T1(1,_1aK/* Questionnaire.formItems526 */),
_1aM/* formItems522 */ = {_:0,a:_1aL/* Questionnaire.formItems525 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1aJ/* Questionnaire.formItems523 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1aN/* formItems512 */ = new T2(5,_1aM/* Questionnaire.formItems522 */,_1aH/* Questionnaire.formItems513 */),
_1aO/* formItems511 */ = new T2(1,_1aN/* Questionnaire.formItems512 */,_k/* GHC.Types.[] */),
_1aP/* formItems527 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1aJ/* Questionnaire.formItems523 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1aQ/* formItems510 */ = new T3(8,_1aP/* Questionnaire.formItems527 */,_Q0/* Questionnaire.formItems31 */,_1aO/* Questionnaire.formItems511 */),
_1aR/* formItems459 */ = new T2(1,_1aQ/* Questionnaire.formItems510 */,_1ay/* Questionnaire.formItems460 */),
_1aS/* formItems530 */ = 60,
_1aT/* formItems529 */ = new T1(1,_1aS/* Questionnaire.formItems530 */),
_1aU/* formItems528 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1aT/* Questionnaire.formItems529 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1aV/* formItems458 */ = new T3(8,_1aU/* Questionnaire.formItems528 */,_Q0/* Questionnaire.formItems31 */,_1aR/* Questionnaire.formItems459 */),
_1aW/* formItems457 */ = new T2(1,_1aV/* Questionnaire.formItems458 */,_k/* GHC.Types.[] */),
_1aX/* formItems456 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_11a/* Questionnaire.formItems432 */,_1aW/* Questionnaire.formItems457 */),
_1aY/* formItems455 */ = new T2(1,_1aX/* Questionnaire.formItems456 */,_k/* GHC.Types.[] */),
_1aZ/* formItems454 */ = new T2(1,_11e/* Questionnaire.formItems40 */,_1aY/* Questionnaire.formItems455 */),
_1b0/* formItems533 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will project partners access the work space?"));
}),
_1b1/* formItems532 */ = new T1(1,_1b0/* Questionnaire.formItems533 */),
_1b2/* formItems531 */ = {_:0,a:_1b1/* Questionnaire.formItems532 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1aT/* Questionnaire.formItems529 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1b3/* formItems453 */ = new T2(5,_1b2/* Questionnaire.formItems531 */,_1aZ/* Questionnaire.formItems454 */),
_1b4/* formItems452 */ = new T2(1,_1b3/* Questionnaire.formItems453 */,_k/* GHC.Types.[] */),
_1b5/* formItems451 */ = new T3(8,_1aU/* Questionnaire.formItems528 */,_Q0/* Questionnaire.formItems31 */,_1b4/* Questionnaire.formItems452 */),
_1b6/* formItems450 */ = new T2(1,_1b5/* Questionnaire.formItems451 */,_k/* GHC.Types.[] */),
_1b7/* formItems542 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Initial data will arrive on separate media and will need to be copied to the work space"));
}),
_1b8/* formItems541 */ = new T1(0,_1b7/* Questionnaire.formItems542 */),
_1b9/* formItems540 */ = new T2(1,_1b8/* Questionnaire.formItems541 */,_k/* GHC.Types.[] */),
_1ba/* formItems544 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We will need a high-speed network connection to copy the initial data"));
}),
_1bb/* formItems543 */ = new T1(0,_1ba/* Questionnaire.formItems544 */),
_1bc/* formItems539 */ = new T2(1,_1bb/* Questionnaire.formItems543 */,_1b9/* Questionnaire.formItems540 */),
_1bd/* formItems546 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Initial data will need to be made available through a local network copy"));
}),
_1be/* formItems545 */ = new T1(0,_1bd/* Questionnaire.formItems546 */),
_1bf/* formItems538 */ = new T2(1,_1be/* Questionnaire.formItems545 */,_1bc/* Questionnaire.formItems539 */),
_1bg/* formItems548 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No special planning is needed for the initial data"));
}),
_1bh/* formItems547 */ = new T1(0,_1bg/* Questionnaire.formItems548 */),
_1bi/* formItems537 */ = new T2(1,_1bh/* Questionnaire.formItems547 */,_1bf/* Questionnaire.formItems538 */),
_1bj/* formItems551 */ = 59,
_1bk/* formItems550 */ = new T1(1,_1bj/* Questionnaire.formItems551 */),
_1bl/* formItems553 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will your first data come in?"));
}),
_1bm/* formItems552 */ = new T1(1,_1bl/* Questionnaire.formItems553 */),
_1bn/* formItems549 */ = {_:0,a:_1bm/* Questionnaire.formItems552 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1bk/* Questionnaire.formItems550 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1bo/* formItems536 */ = new T2(5,_1bn/* Questionnaire.formItems549 */,_1bi/* Questionnaire.formItems537 */),
_1bp/* formItems535 */ = new T2(1,_1bo/* Questionnaire.formItems536 */,_k/* GHC.Types.[] */),
_1bq/* formItems554 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1bk/* Questionnaire.formItems550 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1br/* formItems534 */ = new T3(8,_1bq/* Questionnaire.formItems554 */,_Q0/* Questionnaire.formItems31 */,_1bp/* Questionnaire.formItems535 */),
_1bs/* formItems449 */ = new T2(1,_1br/* Questionnaire.formItems534 */,_1b6/* Questionnaire.formItems450 */),
_1bt/* formItems560 */ = 58,
_1bu/* formItems559 */ = new T1(1,_1bt/* Questionnaire.formItems560 */),
_1bv/* formItems562 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you need to temporarilty archive data sets (to tape)?"));
}),
_1bw/* formItems561 */ = new T1(1,_1bv/* Questionnaire.formItems562 */),
_1bx/* formItems558 */ = {_:0,a:_1bw/* Questionnaire.formItems561 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1bu/* Questionnaire.formItems559 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1by/* formItems557 */ = new T2(5,_1bx/* Questionnaire.formItems558 */,_PW/* Questionnaire.formItems18 */),
_1bz/* formItems556 */ = new T2(1,_1by/* Questionnaire.formItems557 */,_k/* GHC.Types.[] */),
_1bA/* formItems563 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1bu/* Questionnaire.formItems559 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1bB/* formItems555 */ = new T3(8,_1bA/* Questionnaire.formItems563 */,_Q0/* Questionnaire.formItems31 */,_1bz/* Questionnaire.formItems556 */),
_1bC/* formItems448 */ = new T2(1,_1bB/* Questionnaire.formItems555 */,_1bs/* Questionnaire.formItems449 */),
_1bD/* formItems584 */ = 57,
_1bE/* formItems583 */ = new T1(1,_1bD/* Questionnaire.formItems584 */),
_1bF/* formItems586 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Consider storing only the workflow parameters if the data itself could be reproduced quickly</p>"));
}),
_1bG/* formItems585 */ = new T1(1,_1bF/* Questionnaire.formItems586 */),
_1bH/* formItems588 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you have different versions of intermediate data that need to be kept?"));
}),
_1bI/* formItems587 */ = new T1(1,_1bH/* Questionnaire.formItems588 */),
_1bJ/* formItems582 */ = {_:0,a:_1bI/* Questionnaire.formItems587 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_1bG/* Questionnaire.formItems585 */,g:_XM/* Questionnaire.formItems70 */,h:_1bE/* Questionnaire.formItems583 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1bK/* formItems581 */ = new T2(5,_1bJ/* Questionnaire.formItems582 */,_PW/* Questionnaire.formItems18 */),
_1bL/* formItems580 */ = new T2(1,_1bK/* Questionnaire.formItems581 */,_k/* GHC.Types.[] */),
_1bM/* formItems589 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1bE/* Questionnaire.formItems583 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1bN/* formItems579 */ = new T3(8,_1bM/* Questionnaire.formItems589 */,_Q0/* Questionnaire.formItems31 */,_1bL/* Questionnaire.formItems580 */),
_1bO/* formItems578 */ = new T2(1,_1bN/* Questionnaire.formItems579 */,_k/* GHC.Types.[] */),
_1bP/* formItems613 */ = 71,
_1bQ/* formItems612 */ = new T1(1,_1bP/* Questionnaire.formItems613 */),
_1bR/* formItems615 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Are you sure you will not need a backup of the data stored on the scratch file systems (any scratch you use)?"));
}),
_1bS/* formItems614 */ = new T1(1,_1bR/* Questionnaire.formItems615 */),
_1bT/* formItems611 */ = {_:0,a:_1bS/* Questionnaire.formItems614 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1bQ/* Questionnaire.formItems612 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1bU/* formItems610 */ = new T2(5,_1bT/* Questionnaire.formItems611 */,_PW/* Questionnaire.formItems18 */),
_1bV/* formItems609 */ = new T2(1,_1bU/* Questionnaire.formItems610 */,_k/* GHC.Types.[] */),
_1bW/* formItems616 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1bQ/* Questionnaire.formItems612 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1bX/* formItems608 */ = new T3(8,_1bW/* Questionnaire.formItems616 */,_Q0/* Questionnaire.formItems31 */,_1bV/* Questionnaire.formItems609 */),
_1bY/* formItems607 */ = new T2(1,_1bX/* Questionnaire.formItems608 */,_k/* GHC.Types.[] */),
_1bZ/* formItems619 */ = 56,
_1c0/* formItems618 */ = new T1(1,_1bZ/* Questionnaire.formItems619 */),
_1c1/* formItems617 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1c0/* Questionnaire.formItems618 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1c2/* formItems606 */ = new T3(8,_1c1/* Questionnaire.formItems617 */,_Q0/* Questionnaire.formItems31 */,_1bY/* Questionnaire.formItems607 */),
_1c3/* formItems605 */ = new T2(1,_1c2/* Questionnaire.formItems606 */,_k/* GHC.Types.[] */),
_1c4/* formItems620 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We can offload intermediate results to a scratch file system that is not backed up"));
}),
_1c5/* formItems604 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_1c4/* Questionnaire.formItems620 */,_1c3/* Questionnaire.formItems605 */),
_1c6/* formItems603 */ = new T2(1,_1c5/* Questionnaire.formItems604 */,_k/* GHC.Types.[] */),
_1c7/* formItems622 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We will use the main work space for temporary data"));
}),
_1c8/* formItems621 */ = new T1(0,_1c7/* Questionnaire.formItems622 */),
_1c9/* formItems602 */ = new T2(1,_1c8/* Questionnaire.formItems621 */,_1c6/* Questionnaire.formItems603 */),
_1ca/* formItems625 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">If the intermediate results are in your main work space, a restore in case of a problem could take much more time. It may be faster to recover it by re-running computations</p>"));
}),
_1cb/* formItems624 */ = new T1(1,_1ca/* Questionnaire.formItems625 */),
_1cc/* formItems627 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is it possible to store intermediate temporary data on a separate (scratch) file system that is not backed up?"));
}),
_1cd/* formItems626 */ = new T1(1,_1cc/* Questionnaire.formItems627 */),
_1ce/* formItems623 */ = {_:0,a:_1cd/* Questionnaire.formItems626 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_1cb/* Questionnaire.formItems624 */,g:_XM/* Questionnaire.formItems70 */,h:_1c0/* Questionnaire.formItems618 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1cf/* formItems601 */ = new T2(5,_1ce/* Questionnaire.formItems623 */,_1c9/* Questionnaire.formItems602 */),
_1cg/* formItems600 */ = new T2(1,_1cf/* Questionnaire.formItems601 */,_k/* GHC.Types.[] */),
_1ch/* formItems599 */ = new T3(8,_1c1/* Questionnaire.formItems617 */,_Q0/* Questionnaire.formItems31 */,_1cg/* Questionnaire.formItems600 */),
_1ci/* formItems598 */ = new T2(1,_1ch/* Questionnaire.formItems599 */,_k/* GHC.Types.[] */),
_1cj/* formItems630 */ = 55,
_1ck/* formItems629 */ = new T1(1,_1cj/* Questionnaire.formItems630 */),
_1cl/* formItems628 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1ck/* Questionnaire.formItems629 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1cm/* formItems597 */ = new T3(8,_1cl/* Questionnaire.formItems628 */,_Q0/* Questionnaire.formItems31 */,_1ci/* Questionnaire.formItems598 */),
_1cn/* formItems596 */ = new T2(1,_1cm/* Questionnaire.formItems597 */,_k/* GHC.Types.[] */),
_1co/* formItems631 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("A large volume of intermediate data will be in the work space"));
}),
_1cp/* formItems595 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_1co/* Questionnaire.formItems631 */,_1cn/* Questionnaire.formItems596 */),
_1cq/* formItems594 */ = new T2(1,_1cp/* Questionnaire.formItems595 */,_k/* GHC.Types.[] */),
_1cr/* formItems633 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("The volume of intermediate data will not be significant"));
}),
_1cs/* formItems632 */ = new T1(0,_1cr/* Questionnaire.formItems633 */),
_1ct/* formItems593 */ = new T2(1,_1cs/* Questionnaire.formItems632 */,_1cq/* Questionnaire.formItems594 */),
_1cu/* formItems636 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Did you plan how much intermediate data you will get during analysis and how long each step needs to be kept?"));
}),
_1cv/* formItems635 */ = new T1(1,_1cu/* Questionnaire.formItems636 */),
_1cw/* formItems634 */ = {_:0,a:_1cv/* Questionnaire.formItems635 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1ck/* Questionnaire.formItems629 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1cx/* formItems592 */ = new T2(5,_1cw/* Questionnaire.formItems634 */,_1ct/* Questionnaire.formItems593 */),
_1cy/* formItems591 */ = new T2(1,_1cx/* Questionnaire.formItems592 */,_k/* GHC.Types.[] */),
_1cz/* formItems590 */ = new T3(8,_1cl/* Questionnaire.formItems628 */,_Q0/* Questionnaire.formItems31 */,_1cy/* Questionnaire.formItems591 */),
_1cA/* formItems577 */ = new T2(1,_1cz/* Questionnaire.formItems590 */,_1bO/* Questionnaire.formItems578 */),
_1cB/* formItems644 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Raw data do not form a major part of the storage needs"));
}),
_1cC/* formItems643 */ = new T1(0,_1cB/* Questionnaire.formItems644 */),
_1cD/* formItems642 */ = new T2(1,_1cC/* Questionnaire.formItems643 */,_k/* GHC.Types.[] */),
_1cE/* formItems655 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No, it can be remeasured easily and more cheaply than archiving"));
}),
_1cF/* formItems654 */ = new T1(0,_1cE/* Questionnaire.formItems655 */),
_1cG/* formItems653 */ = new T2(1,_1cF/* Questionnaire.formItems654 */,_PT/* Questionnaire.formItems19 */),
_1cH/* formItems657 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No, it is also stored elsewhere can can be recovered easily"));
}),
_1cI/* formItems656 */ = new T1(0,_1cH/* Questionnaire.formItems657 */),
_1cJ/* formItems652 */ = new T2(1,_1cI/* Questionnaire.formItems656 */,_1cG/* Questionnaire.formItems653 */),
_1cK/* formItems660 */ = 54,
_1cL/* formItems659 */ = new T1(1,_1cK/* Questionnaire.formItems660 */),
_1cM/* formItems662 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do your raw data need to be archived?"));
}),
_1cN/* formItems661 */ = new T1(1,_1cM/* Questionnaire.formItems662 */),
_1cO/* formItems658 */ = {_:0,a:_1cN/* Questionnaire.formItems661 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1cL/* Questionnaire.formItems659 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1cP/* formItems651 */ = new T2(5,_1cO/* Questionnaire.formItems658 */,_1cJ/* Questionnaire.formItems652 */),
_1cQ/* formItems650 */ = new T2(1,_1cP/* Questionnaire.formItems651 */,_k/* GHC.Types.[] */),
_1cR/* formItems663 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1cL/* Questionnaire.formItems659 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1cS/* formItems649 */ = new T3(8,_1cR/* Questionnaire.formItems663 */,_Q0/* Questionnaire.formItems31 */,_1cQ/* Questionnaire.formItems650 */),
_1cT/* formItems648 */ = new T2(1,_1cS/* Questionnaire.formItems649 */,_k/* GHC.Types.[] */),
_1cU/* formItems666 */ = 53,
_1cV/* formItems665 */ = new T1(1,_1cU/* Questionnaire.formItems666 */),
_1cW/* formItems664 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1cV/* Questionnaire.formItems665 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1cX/* formItems647 */ = new T3(8,_1cW/* Questionnaire.formItems664 */,_Q0/* Questionnaire.formItems31 */,_1cT/* Questionnaire.formItems648 */),
_1cY/* formItems646 */ = new T2(1,_1cX/* Questionnaire.formItems647 */,_k/* GHC.Types.[] */),
_1cZ/* formItems667 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Raw data can be cleaned out or archived quickly"));
}),
_1d0/* formItems645 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_1cZ/* Questionnaire.formItems667 */,_1cY/* Questionnaire.formItems646 */),
_1d1/* formItems641 */ = new T2(1,_1d0/* Questionnaire.formItems645 */,_1cD/* Questionnaire.formItems642 */),
_1d2/* formItems669 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Raw data will need to stay in the work space"));
}),
_1d3/* formItems668 */ = new T1(0,_1d2/* Questionnaire.formItems669 */),
_1d4/* formItems640 */ = new T2(1,_1d3/* Questionnaire.formItems668 */,_1d1/* Questionnaire.formItems641 */),
_1d5/* formItems672 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Sometimes the raw data is relatively large, and it pays of to clean it quickly.</p>"));
}),
_1d6/* formItems671 */ = new T1(1,_1d5/* Questionnaire.formItems672 */),
_1d7/* formItems674 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How much of the raw data do you need to keep in the work space?"));
}),
_1d8/* formItems673 */ = new T1(1,_1d7/* Questionnaire.formItems674 */),
_1d9/* formItems670 */ = {_:0,a:_1d8/* Questionnaire.formItems673 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_1d6/* Questionnaire.formItems671 */,g:_XM/* Questionnaire.formItems70 */,h:_1cV/* Questionnaire.formItems665 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1da/* formItems639 */ = new T2(5,_1d9/* Questionnaire.formItems670 */,_1d4/* Questionnaire.formItems640 */),
_1db/* formItems638 */ = new T2(1,_1da/* Questionnaire.formItems639 */,_k/* GHC.Types.[] */),
_1dc/* formItems637 */ = new T3(8,_1cW/* Questionnaire.formItems664 */,_Q0/* Questionnaire.formItems31 */,_1db/* Questionnaire.formItems638 */),
_1dd/* formItems576 */ = new T2(1,_1dc/* Questionnaire.formItems637 */,_1cA/* Questionnaire.formItems577 */),
_1de/* formItems681 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Raw data will come in during the project"));
}),
_1df/* formItems680 */ = new T1(0,_1de/* Questionnaire.formItems681 */),
_1dg/* formItems679 */ = new T2(1,_1df/* Questionnaire.formItems680 */,_k/* GHC.Types.[] */),
_1dh/* formItems683 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Raw data will come in right at the start"));
}),
_1di/* formItems682 */ = new T1(0,_1dh/* Questionnaire.formItems683 */),
_1dj/* formItems678 */ = new T2(1,_1di/* Questionnaire.formItems682 */,_1dg/* Questionnaire.formItems679 */),
_1dk/* formItems686 */ = 52,
_1dl/* formItems685 */ = new T1(1,_1dk/* Questionnaire.formItems686 */),
_1dm/* formItems688 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("When will your raw data become available?"));
}),
_1dn/* formItems687 */ = new T1(1,_1dm/* Questionnaire.formItems688 */),
_1do/* formItems684 */ = {_:0,a:_1dn/* Questionnaire.formItems687 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1dl/* Questionnaire.formItems685 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1dp/* formItems677 */ = new T2(5,_1do/* Questionnaire.formItems684 */,_1dj/* Questionnaire.formItems678 */),
_1dq/* formItems676 */ = new T2(1,_1dp/* Questionnaire.formItems677 */,_k/* GHC.Types.[] */),
_1dr/* formItems689 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1dl/* Questionnaire.formItems685 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1ds/* formItems675 */ = new T3(8,_1dr/* Questionnaire.formItems689 */,_Q0/* Questionnaire.formItems31 */,_1dq/* Questionnaire.formItems676 */),
_1dt/* formItems575 */ = new T2(1,_1ds/* Questionnaire.formItems675 */,_1dd/* Questionnaire.formItems576 */),
_1du/* formItems692 */ = 51,
_1dv/* formItems691 */ = new T1(1,_1du/* Questionnaire.formItems692 */),
_1dw/* formItems690 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1dv/* Questionnaire.formItems691 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1dx/* formItems574 */ = new T3(8,_1dw/* Questionnaire.formItems690 */,_Q0/* Questionnaire.formItems31 */,_1dt/* Questionnaire.formItems575 */),
_1dy/* formItems573 */ = new T2(1,_1dx/* Questionnaire.formItems574 */,_k/* GHC.Types.[] */),
_1dz/* formItems572 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_11a/* Questionnaire.formItems432 */,_1dy/* Questionnaire.formItems573 */),
_1dA/* formItems571 */ = new T2(1,_1dz/* Questionnaire.formItems572 */,_k/* GHC.Types.[] */),
_1dB/* formItems694 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Storage needs are largest in the middle of the project"));
}),
_1dC/* formItems693 */ = new T1(0,_1dB/* Questionnaire.formItems694 */),
_1dD/* formItems570 */ = new T2(1,_1dC/* Questionnaire.formItems693 */,_1dA/* Questionnaire.formItems571 */),
_1dE/* formItems696 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Storage needs are small at the beginning and will grow later"));
}),
_1dF/* formItems695 */ = new T1(0,_1dE/* Questionnaire.formItems696 */),
_1dG/* formItems569 */ = new T2(1,_1dF/* Questionnaire.formItems695 */,_1dD/* Questionnaire.formItems570 */),
_1dH/* formItems698 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Storage needs are large at the beginning and will be reduced later"));
}),
_1dI/* formItems697 */ = new T1(0,_1dH/* Questionnaire.formItems698 */),
_1dJ/* formItems568 */ = new T2(1,_1dI/* Questionnaire.formItems697 */,_1dG/* Questionnaire.formItems569 */),
_1dK/* formItems700 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Storage needs will be the same during the whole project"));
}),
_1dL/* formItems699 */ = new T1(0,_1dK/* Questionnaire.formItems700 */),
_1dM/* formItems567 */ = new T2(1,_1dL/* Questionnaire.formItems699 */,_1dJ/* Questionnaire.formItems568 */),
_1dN/* formItems703 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">To perform capacity planning, it is important to know what the need for storage capacity at the beginning and the end of the project will be.</p>"));
}),
_1dO/* formItems702 */ = new T1(1,_1dN/* Questionnaire.formItems703 */),
_1dP/* formItems705 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How does the storage need change over time?"));
}),
_1dQ/* formItems704 */ = new T1(1,_1dP/* Questionnaire.formItems705 */),
_1dR/* formItems701 */ = {_:0,a:_1dQ/* Questionnaire.formItems704 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_1dO/* Questionnaire.formItems702 */,g:_XM/* Questionnaire.formItems70 */,h:_1dv/* Questionnaire.formItems691 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1dS/* formItems566 */ = new T2(5,_1dR/* Questionnaire.formItems701 */,_1dM/* Questionnaire.formItems567 */),
_1dT/* formItems565 */ = new T2(1,_1dS/* Questionnaire.formItems566 */,_k/* GHC.Types.[] */),
_1dU/* formItems564 */ = new T3(8,_1dw/* Questionnaire.formItems690 */,_Q0/* Questionnaire.formItems31 */,_1dT/* Questionnaire.formItems565 */),
_1dV/* formItems447 */ = new T2(1,_1dU/* Questionnaire.formItems564 */,_1bC/* Questionnaire.formItems448 */),
_1dW/* formItems712 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes, archival will require a conversion step"));
}),
_1dX/* formItems711 */ = new T1(0,_1dW/* Questionnaire.formItems712 */),
_1dY/* formItems710 */ = new T2(1,_1dX/* Questionnaire.formItems711 */,_k/* GHC.Types.[] */),
_1dZ/* formItems714 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No, data format will be archived in the same way we work with it"));
}),
_1e0/* formItems713 */ = new T1(0,_1dZ/* Questionnaire.formItems714 */),
_1e1/* formItems709 */ = new T2(1,_1e0/* Questionnaire.formItems713 */,_1dY/* Questionnaire.formItems710 */),
_1e2/* formItems717 */ = 50,
_1e3/* formItems716 */ = new T1(1,_1e2/* Questionnaire.formItems717 */),
_1e4/* formItems719 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Archival and working with data have different requirements. You want archived information to be in a form that others could read and in a format that is also understandable in a number of years. When working with the data, you need to be able to address it efficiently. If the two differ, you need to plan for conversions.</p>"));
}),
_1e5/* formItems718 */ = new T1(1,_1e4/* Questionnaire.formItems719 */),
_1e6/* formItems721 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be working with your data in another form than the way it will be archived?"));
}),
_1e7/* formItems720 */ = new T1(1,_1e6/* Questionnaire.formItems721 */),
_1e8/* formItems715 */ = {_:0,a:_1e7/* Questionnaire.formItems720 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_1e5/* Questionnaire.formItems718 */,g:_XM/* Questionnaire.formItems70 */,h:_1e3/* Questionnaire.formItems716 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1e9/* formItems708 */ = new T2(5,_1e8/* Questionnaire.formItems715 */,_1e1/* Questionnaire.formItems709 */),
_1ea/* formItems707 */ = new T2(1,_1e9/* Questionnaire.formItems708 */,_k/* GHC.Types.[] */),
_1eb/* formItems722 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1e3/* Questionnaire.formItems716 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1ec/* formItems706 */ = new T3(8,_1eb/* Questionnaire.formItems722 */,_Q0/* Questionnaire.formItems31 */,_1ea/* Questionnaire.formItems707 */),
_1ed/* formItems446 */ = new T2(1,_1ec/* Questionnaire.formItems706 */,_1dV/* Questionnaire.formItems447 */),
_1ee/* formItems730 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">If you have large volumes of data that are intensely and repeatedly used by the computing work flow, it may be needed to keep the storage in the same place as where the computing takes place.</p>"));
}),
_1ef/* formItems729 */ = new T1(1,_1ee/* Questionnaire.formItems730 */),
_1eg/* formItems732 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you need the work space to be close to the compute capacity?"));
}),
_1eh/* formItems731 */ = new T1(1,_1eg/* Questionnaire.formItems732 */),
_1ei/* formItems726 */ = {_:0,a:_1eh/* Questionnaire.formItems731 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_1ef/* Questionnaire.formItems729 */,g:_XM/* Questionnaire.formItems70 */,h:_RB/* Questionnaire.formItems727 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1ej/* formItems725 */ = new T2(5,_1ei/* Questionnaire.formItems726 */,_PW/* Questionnaire.formItems18 */),
_1ek/* formItems724 */ = new T2(1,_1ej/* Questionnaire.formItems725 */,_k/* GHC.Types.[] */),
_1el/* formItems733 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_RB/* Questionnaire.formItems727 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1em/* formItems723 */ = new T3(8,_1el/* Questionnaire.formItems733 */,_Q0/* Questionnaire.formItems31 */,_1ek/* Questionnaire.formItems724 */),
_1en/* formItems445 */ = new T2(1,_1em/* Questionnaire.formItems723 */,_1ed/* Questionnaire.formItems446 */),
_1eo/* formItems741 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("When making the work space, it helps to know whether you expect to work with very many small files, a few very large files, whether you will use a (SQL) database to store most of the data. Maybe your data is suitable for a system like Hadoop? Such information can be collected here."));
}),
_1ep/* formItems740 */ = new T1(1,_1eo/* Questionnaire.formItems741 */),
_1eq/* formItems743 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What kind of data will you have in your work space?"));
}),
_1er/* formItems742 */ = new T1(1,_1eq/* Questionnaire.formItems743 */),
_1es/* formItems737 */ = {_:0,a:_1er/* Questionnaire.formItems742 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_1ep/* Questionnaire.formItems740 */,g:_XM/* Questionnaire.formItems70 */,h:_RL/* Questionnaire.formItems738 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1et/* formItems736 */ = new T1(1,_1es/* Questionnaire.formItems737 */),
_1eu/* formItems735 */ = new T2(1,_1et/* Questionnaire.formItems736 */,_k/* GHC.Types.[] */),
_1ev/* formItems744 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_RL/* Questionnaire.formItems738 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1ew/* formItems734 */ = new T3(8,_1ev/* Questionnaire.formItems744 */,_Q0/* Questionnaire.formItems31 */,_1eu/* Questionnaire.formItems735 */),
_1ex/* formItems444 */ = new T2(1,_1ew/* Questionnaire.formItems734 */,_1en/* Questionnaire.formItems445 */),
_1ey/* formItems745 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_S1/* Questionnaire.formItems746 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1ez/* formItems443 */ = new T3(8,_1ey/* Questionnaire.formItems745 */,_Q0/* Questionnaire.formItems31 */,_1ex/* Questionnaire.formItems444 */),
_1eA/* formItems442 */ = new T2(1,_1ez/* Questionnaire.formItems443 */,_k/* GHC.Types.[] */),
_1eB/* formItems441 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_11a/* Questionnaire.formItems432 */,_1eA/* Questionnaire.formItems442 */),
_1eC/* formItems440 */ = new T2(1,_1eB/* Questionnaire.formItems441 */,_k/* GHC.Types.[] */),
_1eD/* formItems439 */ = new T2(1,_11e/* Questionnaire.formItems40 */,_1eC/* Questionnaire.formItems440 */),
_1eE/* formItems750 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you work with your data?"));
}),
_1eF/* formItems749 */ = new T1(1,_1eE/* Questionnaire.formItems750 */),
_1eG/* formItems748 */ = {_:0,a:_1eF/* Questionnaire.formItems749 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_S1/* Questionnaire.formItems746 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1eH/* formItems438 */ = new T2(5,_1eG/* Questionnaire.formItems748 */,_1eD/* Questionnaire.formItems439 */),
_1eI/* formItems437 */ = new T2(1,_1eH/* Questionnaire.formItems438 */,_k/* GHC.Types.[] */),
_1eJ/* formItems436 */ = new T3(8,_1ey/* Questionnaire.formItems745 */,_Q0/* Questionnaire.formItems31 */,_1eI/* Questionnaire.formItems437 */),
_1eK/* formItems304 */ = new T2(1,_1eJ/* Questionnaire.formItems436 */,_19K/* Questionnaire.formItems305 */),
_1eL/* formItems751 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Sd/* Questionnaire.formItems752 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1eM/* formItems303 */ = new T3(8,_1eL/* Questionnaire.formItems751 */,_Q0/* Questionnaire.formItems31 */,_1eK/* Questionnaire.formItems304 */),
_1eN/* formItems302 */ = new T2(1,_1eM/* Questionnaire.formItems303 */,_k/* GHC.Types.[] */),
_1eO/* formItems301 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_1eN/* Questionnaire.formItems302 */),
_1eP/* formItems300 */ = new T2(1,_1eO/* Questionnaire.formItems301 */,_k/* GHC.Types.[] */),
_1eQ/* formItems764 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes, protected against both equipment failure and human error"));
}),
_1eR/* formItems763 */ = new T1(0,_1eQ/* Questionnaire.formItems764 */),
_1eS/* formItems762 */ = new T2(1,_1eR/* Questionnaire.formItems763 */,_k/* GHC.Types.[] */),
_1eT/* formItems761 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_1eS/* Questionnaire.formItems762 */),
_1eU/* formItems767 */ = 73,
_1eV/* formItems766 */ = new T1(1,_1eU/* Questionnaire.formItems767 */),
_1eW/* formItems769 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Are data all project members store adequately backed up and traceable?"));
}),
_1eX/* formItems768 */ = new T1(1,_1eW/* Questionnaire.formItems769 */),
_1eY/* formItems765 */ = {_:0,a:_1eX/* Questionnaire.formItems768 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1eV/* Questionnaire.formItems766 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1eZ/* formItems760 */ = new T2(5,_1eY/* Questionnaire.formItems765 */,_1eT/* Questionnaire.formItems761 */),
_1f0/* formItems759 */ = new T2(1,_1eZ/* Questionnaire.formItems760 */,_k/* GHC.Types.[] */),
_1f1/* formItems770 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1eV/* Questionnaire.formItems766 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1f2/* formItems758 */ = new T3(8,_1f1/* Questionnaire.formItems770 */,_Q0/* Questionnaire.formItems31 */,_1f0/* Questionnaire.formItems759 */),
_1f3/* formItems757 */ = new T2(1,_1f2/* Questionnaire.formItems758 */,_k/* GHC.Types.[] */),
_1f4/* formItems756 */ = new T3(8,_1eL/* Questionnaire.formItems751 */,_Q0/* Questionnaire.formItems31 */,_1f3/* Questionnaire.formItems757 */),
_1f5/* formItems755 */ = new T2(1,_1f4/* Questionnaire.formItems756 */,_k/* GHC.Types.[] */),
_1f6/* formItems754 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PU/* Questionnaire.formItems23 */,_1f5/* Questionnaire.formItems755 */),
_1f7/* formItems299 */ = new T2(1,_1f6/* Questionnaire.formItems754 */,_1eP/* Questionnaire.formItems300 */),
_1f8/* formItems773 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you need a shared working space to work with your data?"));
}),
_1f9/* formItems772 */ = new T1(1,_1f8/* Questionnaire.formItems773 */),
_1fa/* formItems771 */ = {_:0,a:_1f9/* Questionnaire.formItems772 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Sd/* Questionnaire.formItems752 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1fb/* formItems298 */ = new T2(5,_1fa/* Questionnaire.formItems771 */,_1f7/* Questionnaire.formItems299 */),
_1fc/* formItems297 */ = new T2(1,_1fb/* Questionnaire.formItems298 */,_k/* GHC.Types.[] */),
_1fd/* formItems296 */ = new T3(8,_1eL/* Questionnaire.formItems751 */,_Q0/* Questionnaire.formItems31 */,_1fc/* Questionnaire.formItems297 */),
_1fe/* formItems295 */ = new T2(1,_1fd/* Questionnaire.formItems296 */,_k/* GHC.Types.[] */),
_1ff/* formItems1030 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be archiving data for long term preservation?"));
}),
_1fg/* formItems1029 */ = new T1(1,_1ff/* Questionnaire.formItems1030 */),
_1fh/* formItems995 */ = 26,
_1fi/* formItems994 */ = new T1(1,_1fh/* Questionnaire.formItems995 */),
_1fj/* formItems1028 */ = {_:0,a:_1fg/* Questionnaire.formItems1029 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1fi/* Questionnaire.formItems994 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1fk/* formItems797 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">See also all questions about keeping metadata and data formats. Make sure the metadata is kept close to the data in the archive, and that community supported data formats are used for all long term archiving.</p>"));
}),
_1fl/* formItems796 */ = new T1(1,_1fk/* Questionnaire.formItems797 */),
_1fm/* formItems799 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will the data still be understandable after a long time?"));
}),
_1fn/* formItems798 */ = new T1(1,_1fm/* Questionnaire.formItems799 */),
_1fo/* formItems793 */ = {_:0,a:_1fn/* Questionnaire.formItems798 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_1fl/* Questionnaire.formItems796 */,g:_XM/* Questionnaire.formItems70 */,h:_Sn/* Questionnaire.formItems794 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1fp/* formItems792 */ = new T2(5,_1fo/* Questionnaire.formItems793 */,_PW/* Questionnaire.formItems18 */),
_1fq/* formItems791 */ = new T2(1,_1fp/* Questionnaire.formItems792 */,_k/* GHC.Types.[] */),
_1fr/* formItems800 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Sn/* Questionnaire.formItems794 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1fs/* formItems790 */ = new T3(8,_1fr/* Questionnaire.formItems800 */,_Q0/* Questionnaire.formItems31 */,_1fq/* Questionnaire.formItems791 */),
_1ft/* formItems789 */ = new T2(1,_1fs/* Questionnaire.formItems790 */,_k/* GHC.Types.[] */),
_1fu/* formItems808 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Has it been established how long the archived data need to be kept? For each of the different parts of the archive (raw data / results)?"));
}),
_1fv/* formItems807 */ = new T1(1,_1fu/* Questionnaire.formItems808 */),
_1fw/* formItems804 */ = {_:0,a:_1fv/* Questionnaire.formItems807 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Sz/* Questionnaire.formItems805 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1fx/* formItems803 */ = new T2(5,_1fw/* Questionnaire.formItems804 */,_PW/* Questionnaire.formItems18 */),
_1fy/* formItems802 */ = new T2(1,_1fx/* Questionnaire.formItems803 */,_k/* GHC.Types.[] */),
_1fz/* formItems809 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Sz/* Questionnaire.formItems805 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1fA/* formItems801 */ = new T3(8,_1fz/* Questionnaire.formItems809 */,_Q0/* Questionnaire.formItems31 */,_1fy/* Questionnaire.formItems802 */),
_1fB/* formItems788 */ = new T2(1,_1fA/* Questionnaire.formItems801 */,_1ft/* Questionnaire.formItems789 */),
_1fC/* formItems828 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("has authority over the data been arranged for when the project is finished (potentially long ago)? Is there a data access committee?"));
}),
_1fD/* formItems827 */ = new T1(1,_1fC/* Questionnaire.formItems828 */),
_1fE/* formItems824 */ = {_:0,a:_1fD/* Questionnaire.formItems827 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_SL/* Questionnaire.formItems825 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1fF/* formItems823 */ = new T2(5,_1fE/* Questionnaire.formItems824 */,_PW/* Questionnaire.formItems18 */),
_1fG/* formItems822 */ = new T2(1,_1fF/* Questionnaire.formItems823 */,_k/* GHC.Types.[] */),
_1fH/* formItems829 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_SL/* Questionnaire.formItems825 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1fI/* formItems821 */ = new T3(8,_1fH/* Questionnaire.formItems829 */,_Q0/* Questionnaire.formItems31 */,_1fG/* Questionnaire.formItems822 */),
_1fJ/* formItems820 */ = new T2(1,_1fI/* Questionnaire.formItems821 */,_k/* GHC.Types.[] */),
_1fK/* formItems837 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("If the data is voluminous, will the project be able to cope with the time needed for a restore?"));
}),
_1fL/* formItems836 */ = new T1(1,_1fK/* Questionnaire.formItems837 */),
_1fM/* formItems833 */ = {_:0,a:_1fL/* Questionnaire.formItems836 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_ST/* Questionnaire.formItems834 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1fN/* formItems832 */ = new T2(5,_1fM/* Questionnaire.formItems833 */,_PW/* Questionnaire.formItems18 */),
_1fO/* formItems831 */ = new T2(1,_1fN/* Questionnaire.formItems832 */,_k/* GHC.Types.[] */),
_1fP/* formItems838 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_ST/* Questionnaire.formItems834 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1fQ/* formItems830 */ = new T3(8,_1fP/* Questionnaire.formItems838 */,_Q0/* Questionnaire.formItems31 */,_1fO/* Questionnaire.formItems831 */),
_1fR/* formItems819 */ = new T2(1,_1fQ/* Questionnaire.formItems830 */,_1fJ/* Questionnaire.formItems820 */),
_1fS/* formItems844 */ = 41,
_1fT/* formItems843 */ = new T1(1,_1fS/* Questionnaire.formItems844 */),
_1fU/* formItems846 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Has it been established who can ask for a restore during the project?"));
}),
_1fV/* formItems845 */ = new T1(1,_1fU/* Questionnaire.formItems846 */),
_1fW/* formItems842 */ = {_:0,a:_1fV/* Questionnaire.formItems845 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1fT/* Questionnaire.formItems843 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1fX/* formItems841 */ = new T2(5,_1fW/* Questionnaire.formItems842 */,_PW/* Questionnaire.formItems18 */),
_1fY/* formItems840 */ = new T2(1,_1fX/* Questionnaire.formItems841 */,_k/* GHC.Types.[] */),
_1fZ/* formItems847 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1fT/* Questionnaire.formItems843 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1g0/* formItems839 */ = new T3(8,_1fZ/* Questionnaire.formItems847 */,_Q0/* Questionnaire.formItems31 */,_1fY/* Questionnaire.formItems840 */),
_1g1/* formItems818 */ = new T2(1,_1g0/* Questionnaire.formItems839 */,_1fR/* Questionnaire.formItems819 */),
_1g2/* formItems850 */ = 40,
_1g3/* formItems849 */ = new T1(1,_1g2/* Questionnaire.formItems850 */),
_1g4/* formItems848 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1g3/* Questionnaire.formItems849 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1g5/* formItems817 */ = new T3(8,_1g4/* Questionnaire.formItems848 */,_Q0/* Questionnaire.formItems31 */,_1g1/* Questionnaire.formItems818 */),
_1g6/* formItems816 */ = new T2(1,_1g5/* Questionnaire.formItems817 */,_k/* GHC.Types.[] */),
_1g7/* formItems815 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_1g6/* Questionnaire.formItems816 */),
_1g8/* formItems814 */ = new T2(1,_1g7/* Questionnaire.formItems815 */,_k/* GHC.Types.[] */),
_1g9/* formItems813 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_1g8/* Questionnaire.formItems814 */),
_1ga/* formItems853 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Has it been established who has access to the archive, and how fast?"));
}),
_1gb/* formItems852 */ = new T1(1,_1ga/* Questionnaire.formItems853 */),
_1gc/* formItems851 */ = {_:0,a:_1gb/* Questionnaire.formItems852 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1g3/* Questionnaire.formItems849 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1gd/* formItems812 */ = new T2(5,_1gc/* Questionnaire.formItems851 */,_1g9/* Questionnaire.formItems813 */),
_1ge/* formItems811 */ = new T2(1,_1gd/* Questionnaire.formItems812 */,_k/* GHC.Types.[] */),
_1gf/* formItems810 */ = new T3(8,_1g4/* Questionnaire.formItems848 */,_Q0/* Questionnaire.formItems31 */,_1ge/* Questionnaire.formItems811 */),
_1gg/* formItems787 */ = new T2(1,_1gf/* Questionnaire.formItems810 */,_1fB/* Questionnaire.formItems788 */),
_1gh/* formItems868 */ = 39,
_1gi/* formItems867 */ = new T1(1,_1gh/* Questionnaire.formItems868 */),
_1gj/* formItems870 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">If the \'master copy\' of the data is available on line, it should probably be protected against being tampered with.</p>"));
}),
_1gk/* formItems869 */ = new T1(1,_1gj/* Questionnaire.formItems870 */),
_1gl/* formItems872 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will data integrity be guaranteed?"));
}),
_1gm/* formItems871 */ = new T1(1,_1gl/* Questionnaire.formItems872 */),
_1gn/* formItems866 */ = {_:0,a:_1gm/* Questionnaire.formItems871 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_1gk/* Questionnaire.formItems869 */,g:_XM/* Questionnaire.formItems70 */,h:_1gi/* Questionnaire.formItems867 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1go/* formItems865 */ = new T2(5,_1gn/* Questionnaire.formItems866 */,_PW/* Questionnaire.formItems18 */),
_1gp/* formItems864 */ = new T2(1,_1go/* Questionnaire.formItems865 */,_k/* GHC.Types.[] */),
_1gq/* formItems873 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1gi/* Questionnaire.formItems867 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1gr/* formItems863 */ = new T3(8,_1gq/* Questionnaire.formItems873 */,_Q0/* Questionnaire.formItems31 */,_1gp/* Questionnaire.formItems864 */),
_1gs/* formItems862 */ = new T2(1,_1gr/* Questionnaire.formItems863 */,_k/* GHC.Types.[] */),
_1gt/* formItems874 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_PP/* Questionnaire.formItems875 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1gu/* formItems861 */ = new T3(8,_1gt/* Questionnaire.formItems874 */,_Q0/* Questionnaire.formItems31 */,_1gs/* Questionnaire.formItems862 */),
_1gv/* formItems860 */ = new T2(1,_1gu/* Questionnaire.formItems861 */,_k/* GHC.Types.[] */),
_1gw/* formItems859 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_1gv/* Questionnaire.formItems860 */),
_1gx/* formItems858 */ = new T2(1,_1gw/* Questionnaire.formItems859 */,_k/* GHC.Types.[] */),
_1gy/* formItems857 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_1gx/* Questionnaire.formItems858 */),
_1gz/* formItems879 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will your project require the archives to be available on-line?"));
}),
_1gA/* formItems878 */ = new T1(1,_1gz/* Questionnaire.formItems879 */),
_1gB/* formItems877 */ = {_:0,a:_1gA/* Questionnaire.formItems878 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_PP/* Questionnaire.formItems875 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1gC/* formItems856 */ = new T2(5,_1gB/* Questionnaire.formItems877 */,_1gy/* Questionnaire.formItems857 */),
_1gD/* formItems855 */ = new T2(1,_1gC/* Questionnaire.formItems856 */,_k/* GHC.Types.[] */),
_1gE/* formItems854 */ = new T3(8,_1gt/* Questionnaire.formItems874 */,_Q0/* Questionnaire.formItems31 */,_1gD/* Questionnaire.formItems855 */),
_1gF/* formItems786 */ = new T2(1,_1gE/* Questionnaire.formItems854 */,_1gg/* Questionnaire.formItems787 */),
_1gG/* formItems895 */ = 37,
_1gH/* formItems894 */ = new T1(1,_1gG/* Questionnaire.formItems895 */),
_1gI/* formItems897 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is it clear who has physical access to the archives?"));
}),
_1gJ/* formItems896 */ = new T1(1,_1gI/* Questionnaire.formItems897 */),
_1gK/* formItems893 */ = {_:0,a:_1gJ/* Questionnaire.formItems896 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1gH/* Questionnaire.formItems894 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1gL/* formItems892 */ = new T2(5,_1gK/* Questionnaire.formItems893 */,_PW/* Questionnaire.formItems18 */),
_1gM/* formItems891 */ = new T2(1,_1gL/* Questionnaire.formItems892 */,_k/* GHC.Types.[] */),
_1gN/* formItems898 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1gH/* Questionnaire.formItems894 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1gO/* formItems890 */ = new T3(8,_1gN/* Questionnaire.formItems898 */,_Q0/* Questionnaire.formItems31 */,_1gM/* Questionnaire.formItems891 */),
_1gP/* formItems889 */ = new T2(1,_1gO/* Questionnaire.formItems890 */,_k/* GHC.Types.[] */),
_1gQ/* formItems913 */ = 36,
_1gR/* formItems912 */ = new T1(1,_1gQ/* Questionnaire.formItems913 */),
_1gS/* formItems915 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is it clear who has access to the key? Also in case of a required data restore?"));
}),
_1gT/* formItems914 */ = new T1(1,_1gS/* Questionnaire.formItems915 */),
_1gU/* formItems911 */ = {_:0,a:_1gT/* Questionnaire.formItems914 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1gR/* Questionnaire.formItems912 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1gV/* formItems910 */ = new T2(5,_1gU/* Questionnaire.formItems911 */,_PW/* Questionnaire.formItems18 */),
_1gW/* formItems909 */ = new T2(1,_1gV/* Questionnaire.formItems910 */,_k/* GHC.Types.[] */),
_1gX/* formItems916 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1gR/* Questionnaire.formItems912 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1gY/* formItems908 */ = new T3(8,_1gX/* Questionnaire.formItems916 */,_Q0/* Questionnaire.formItems31 */,_1gW/* Questionnaire.formItems909 */),
_1gZ/* formItems907 */ = new T2(1,_1gY/* Questionnaire.formItems908 */,_k/* GHC.Types.[] */),
_1h0/* formItems919 */ = 35,
_1h1/* formItems918 */ = new T1(1,_1h0/* Questionnaire.formItems919 */),
_1h2/* formItems917 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1h1/* Questionnaire.formItems918 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1h3/* formItems906 */ = new T3(8,_1h2/* Questionnaire.formItems917 */,_Q0/* Questionnaire.formItems31 */,_1gZ/* Questionnaire.formItems907 */),
_1h4/* formItems905 */ = new T2(1,_1h3/* Questionnaire.formItems906 */,_k/* GHC.Types.[] */),
_1h5/* formItems904 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_1h4/* Questionnaire.formItems905 */),
_1h6/* formItems903 */ = new T2(1,_1h5/* Questionnaire.formItems904 */,_k/* GHC.Types.[] */),
_1h7/* formItems902 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_1h6/* Questionnaire.formItems903 */),
_1h8/* formItems922 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will the archive be encrypted?"));
}),
_1h9/* formItems921 */ = new T1(1,_1h8/* Questionnaire.formItems922 */),
_1ha/* formItems920 */ = {_:0,a:_1h9/* Questionnaire.formItems921 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1h1/* Questionnaire.formItems918 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1hb/* formItems901 */ = new T2(5,_1ha/* Questionnaire.formItems920 */,_1h7/* Questionnaire.formItems902 */),
_1hc/* formItems900 */ = new T2(1,_1hb/* Questionnaire.formItems901 */,_k/* GHC.Types.[] */),
_1hd/* formItems899 */ = new T3(8,_1h2/* Questionnaire.formItems917 */,_Q0/* Questionnaire.formItems31 */,_1hc/* Questionnaire.formItems900 */),
_1he/* formItems888 */ = new T2(1,_1hd/* Questionnaire.formItems899 */,_1gP/* Questionnaire.formItems889 */),
_1hf/* formItems925 */ = 34,
_1hg/* formItems924 */ = new T1(1,_1hf/* Questionnaire.formItems925 */),
_1hh/* formItems923 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1hg/* Questionnaire.formItems924 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1hi/* formItems887 */ = new T3(8,_1hh/* Questionnaire.formItems923 */,_Q0/* Questionnaire.formItems31 */,_1he/* Questionnaire.formItems888 */),
_1hj/* formItems886 */ = new T2(1,_1hi/* Questionnaire.formItems887 */,_k/* GHC.Types.[] */),
_1hk/* formItems885 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_1hj/* Questionnaire.formItems886 */),
_1hl/* formItems884 */ = new T2(1,_1hk/* Questionnaire.formItems885 */,_k/* GHC.Types.[] */),
_1hm/* formItems883 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_1hl/* Questionnaire.formItems884 */),
_1hn/* formItems928 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will the archive need to be protected against loss or theft?"));
}),
_1ho/* formItems927 */ = new T1(1,_1hn/* Questionnaire.formItems928 */),
_1hp/* formItems926 */ = {_:0,a:_1ho/* Questionnaire.formItems927 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1hg/* Questionnaire.formItems924 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1hq/* formItems882 */ = new T2(5,_1hp/* Questionnaire.formItems926 */,_1hm/* Questionnaire.formItems883 */),
_1hr/* formItems881 */ = new T2(1,_1hq/* Questionnaire.formItems882 */,_k/* GHC.Types.[] */),
_1hs/* formItems880 */ = new T3(8,_1hh/* Questionnaire.formItems923 */,_Q0/* Questionnaire.formItems31 */,_1hr/* Questionnaire.formItems881 */),
_1ht/* formItems785 */ = new T2(1,_1hs/* Questionnaire.formItems880 */,_1gF/* Questionnaire.formItems786 */),
_1hu/* formItems936 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will the archive be stored in a remote location, protecting the data against disasters?"));
}),
_1hv/* formItems935 */ = new T1(1,_1hu/* Questionnaire.formItems936 */),
_1hw/* formItems932 */ = {_:0,a:_1hv/* Questionnaire.formItems935 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Q6/* Questionnaire.formItems933 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1hx/* formItems931 */ = new T2(5,_1hw/* Questionnaire.formItems932 */,_PW/* Questionnaire.formItems18 */),
_1hy/* formItems930 */ = new T2(1,_1hx/* Questionnaire.formItems931 */,_k/* GHC.Types.[] */),
_1hz/* formItems937 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Q6/* Questionnaire.formItems933 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1hA/* formItems929 */ = new T3(8,_1hz/* Questionnaire.formItems937 */,_Q0/* Questionnaire.formItems31 */,_1hy/* Questionnaire.formItems930 */),
_1hB/* formItems784 */ = new T2(1,_1hA/* Questionnaire.formItems929 */,_1ht/* Questionnaire.formItems785 */),
_1hC/* formItems944 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tape"));
}),
_1hD/* formItems943 */ = new T1(0,_1hC/* Questionnaire.formItems944 */),
_1hE/* formItems942 */ = new T2(1,_1hD/* Questionnaire.formItems943 */,_k/* GHC.Types.[] */),
_1hF/* formItems946 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Disc"));
}),
_1hG/* formItems945 */ = new T1(0,_1hF/* Questionnaire.formItems946 */),
_1hH/* formItems941 */ = new T2(1,_1hG/* Questionnaire.formItems945 */,_1hE/* Questionnaire.formItems942 */),
_1hI/* formItems951 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will the archive be stored on disc or on tape?"));
}),
_1hJ/* formItems950 */ = new T1(1,_1hI/* Questionnaire.formItems951 */),
_1hK/* formItems947 */ = {_:0,a:_1hJ/* Questionnaire.formItems950 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Qi/* Questionnaire.formItems948 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1hL/* formItems940 */ = new T2(5,_1hK/* Questionnaire.formItems947 */,_1hH/* Questionnaire.formItems941 */),
_1hM/* formItems939 */ = new T2(1,_1hL/* Questionnaire.formItems940 */,_k/* GHC.Types.[] */),
_1hN/* formItems952 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Qi/* Questionnaire.formItems948 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1hO/* formItems938 */ = new T3(8,_1hN/* Questionnaire.formItems952 */,_Q0/* Questionnaire.formItems31 */,_1hM/* Questionnaire.formItems939 */),
_1hP/* formItems783 */ = new T2(1,_1hO/* Questionnaire.formItems938 */,_1hB/* Questionnaire.formItems784 */),
_1hQ/* formItems970 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be relying on these backups to recover from human error (accidental changes or deletions)?"));
}),
_1hR/* formItems969 */ = new T1(1,_1hQ/* Questionnaire.formItems970 */),
_1hS/* formItems966 */ = {_:0,a:_1hR/* Questionnaire.formItems969 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Qu/* Questionnaire.formItems967 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1hT/* formItems965 */ = new T2(5,_1hS/* Questionnaire.formItems966 */,_PW/* Questionnaire.formItems18 */),
_1hU/* formItems964 */ = new T2(1,_1hT/* Questionnaire.formItems965 */,_k/* GHC.Types.[] */),
_1hV/* formItems971 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_Qu/* Questionnaire.formItems967 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1hW/* formItems963 */ = new T3(8,_1hV/* Questionnaire.formItems971 */,_Q0/* Questionnaire.formItems31 */,_1hU/* Questionnaire.formItems964 */),
_1hX/* formItems962 */ = new T2(1,_1hW/* Questionnaire.formItems963 */,_k/* GHC.Types.[] */),
_1hY/* formItems978 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes, data changes frequently"));
}),
_1hZ/* formItems977 */ = new T1(0,_1hY/* Questionnaire.formItems978 */),
_1i0/* formItems976 */ = new T2(1,_1hZ/* Questionnaire.formItems977 */,_k/* GHC.Types.[] */),
_1i1/* formItems980 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No, data changes infrequently"));
}),
_1i2/* formItems979 */ = new T1(0,_1i1/* Questionnaire.formItems980 */),
_1i3/* formItems975 */ = new T2(1,_1i2/* Questionnaire.formItems979 */,_1i0/* Questionnaire.formItems976 */),
_1i4/* formItems985 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you need frequent backups?"));
}),
_1i5/* formItems984 */ = new T1(1,_1i4/* Questionnaire.formItems985 */),
_1i6/* formItems981 */ = {_:0,a:_1i5/* Questionnaire.formItems984 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_QO/* Questionnaire.formItems982 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1i7/* formItems974 */ = new T2(5,_1i6/* Questionnaire.formItems981 */,_1i3/* Questionnaire.formItems975 */),
_1i8/* formItems973 */ = new T2(1,_1i7/* Questionnaire.formItems974 */,_k/* GHC.Types.[] */),
_1i9/* formItems986 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_QO/* Questionnaire.formItems982 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1ia/* formItems972 */ = new T3(8,_1i9/* Questionnaire.formItems986 */,_Q0/* Questionnaire.formItems31 */,_1i8/* Questionnaire.formItems973 */),
_1ib/* formItems961 */ = new T2(1,_1ia/* Questionnaire.formItems972 */,_1hX/* Questionnaire.formItems962 */),
_1ic/* formItems989 */ = 28,
_1id/* formItems988 */ = new T1(1,_1ic/* Questionnaire.formItems989 */),
_1ie/* formItems987 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1id/* Questionnaire.formItems988 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1if/* formItems960 */ = new T3(8,_1ie/* Questionnaire.formItems987 */,_Q0/* Questionnaire.formItems31 */,_1ib/* Questionnaire.formItems961 */),
_1ig/* formItems959 */ = new T2(1,_1if/* Questionnaire.formItems960 */,_k/* GHC.Types.[] */),
_1ih/* formItems958 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_1ig/* Questionnaire.formItems959 */),
_1ii/* formItems957 */ = new T2(1,_1ih/* Questionnaire.formItems958 */,_k/* GHC.Types.[] */),
_1ij/* formItems956 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_1ii/* Questionnaire.formItems957 */),
_1ik/* formItems992 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is the archived data changing over time, needing re-archival?"));
}),
_1il/* formItems991 */ = new T1(1,_1ik/* Questionnaire.formItems992 */),
_1im/* formItems990 */ = {_:0,a:_1il/* Questionnaire.formItems991 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1id/* Questionnaire.formItems988 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1in/* formItems955 */ = new T2(5,_1im/* Questionnaire.formItems990 */,_1ij/* Questionnaire.formItems956 */),
_1io/* formItems954 */ = new T2(1,_1in/* Questionnaire.formItems955 */,_k/* GHC.Types.[] */),
_1ip/* formItems953 */ = new T3(8,_1ie/* Questionnaire.formItems987 */,_Q0/* Questionnaire.formItems31 */,_1io/* Questionnaire.formItems954 */),
_1iq/* formItems782 */ = new T2(1,_1ip/* Questionnaire.formItems953 */,_1hP/* Questionnaire.formItems783 */),
_1ir/* formItems993 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1fi/* Questionnaire.formItems994 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1is/* formItems781 */ = new T3(8,_1ir/* Questionnaire.formItems993 */,_Q0/* Questionnaire.formItems31 */,_1iq/* Questionnaire.formItems782 */),
_1it/* formItems780 */ = new T2(1,_1is/* Questionnaire.formItems781 */,_k/* GHC.Types.[] */),
_1iu/* formItems779 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_1it/* Questionnaire.formItems780 */),
_1iv/* formItems778 */ = new T2(1,_1iu/* Questionnaire.formItems779 */,_k/* GHC.Types.[] */),
_1iw/* formItems1008 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("All at once with the results at the end of the project"));
}),
_1ix/* formItems1007 */ = new T1(0,_1iw/* Questionnaire.formItems1008 */),
_1iy/* formItems1006 */ = new T2(1,_1ix/* Questionnaire.formItems1007 */,_k/* GHC.Types.[] */),
_1iz/* formItems1010 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("As soon as it has all arrived, in one session"));
}),
_1iA/* formItems1009 */ = new T1(0,_1iz/* Questionnaire.formItems1010 */),
_1iB/* formItems1005 */ = new T2(1,_1iA/* Questionnaire.formItems1009 */,_1iy/* Questionnaire.formItems1006 */),
_1iC/* formItems1012 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("As soon as it comes in, in chunks"));
}),
_1iD/* formItems1011 */ = new T1(0,_1iC/* Questionnaire.formItems1012 */),
_1iE/* formItems1004 */ = new T2(1,_1iD/* Questionnaire.formItems1011 */,_1iB/* Questionnaire.formItems1005 */),
_1iF/* formItems1017 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("When is the raw data archived?"));
}),
_1iG/* formItems1016 */ = new T1(1,_1iF/* Questionnaire.formItems1017 */),
_1iH/* formItems1013 */ = {_:0,a:_1iG/* Questionnaire.formItems1016 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_QC/* Questionnaire.formItems1014 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1iI/* formItems1003 */ = new T2(5,_1iH/* Questionnaire.formItems1013 */,_1iE/* Questionnaire.formItems1004 */),
_1iJ/* formItems1002 */ = new T2(1,_1iI/* Questionnaire.formItems1003 */,_k/* GHC.Types.[] */),
_1iK/* formItems1018 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_QC/* Questionnaire.formItems1014 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1iL/* formItems1001 */ = new T3(8,_1iK/* Questionnaire.formItems1018 */,_Q0/* Questionnaire.formItems31 */,_1iJ/* Questionnaire.formItems1002 */),
_1iM/* formItems1000 */ = new T2(1,_1iL/* Questionnaire.formItems1001 */,_k/* GHC.Types.[] */),
_1iN/* formItems1024 */ = 27,
_1iO/* formItems1023 */ = new T1(1,_1iN/* Questionnaire.formItems1024 */),
_1iP/* formItems1026 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Can the original data be recreated?"));
}),
_1iQ/* formItems1025 */ = new T1(1,_1iP/* Questionnaire.formItems1026 */),
_1iR/* formItems1022 */ = {_:0,a:_1iQ/* Questionnaire.formItems1025 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1iO/* Questionnaire.formItems1023 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1iS/* formItems1021 */ = new T2(5,_1iR/* Questionnaire.formItems1022 */,_PW/* Questionnaire.formItems18 */),
_1iT/* formItems1020 */ = new T2(1,_1iS/* Questionnaire.formItems1021 */,_k/* GHC.Types.[] */),
_1iU/* formItems1027 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_XM/* Questionnaire.formItems70 */,h:_1iO/* Questionnaire.formItems1023 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1iV/* formItems1019 */ = new T3(8,_1iU/* Questionnaire.formItems1027 */,_Q0/* Questionnaire.formItems31 */,_1iT/* Questionnaire.formItems1020 */),
_1iW/* formItems999 */ = new T2(1,_1iV/* Questionnaire.formItems1019 */,_1iM/* Questionnaire.formItems1000 */),
_1iX/* formItems998 */ = new T3(8,_1ir/* Questionnaire.formItems993 */,_Q0/* Questionnaire.formItems31 */,_1iW/* Questionnaire.formItems999 */),
_1iY/* formItems997 */ = new T2(1,_1iX/* Questionnaire.formItems998 */,_k/* GHC.Types.[] */),
_1iZ/* formItems996 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PU/* Questionnaire.formItems23 */,_1iY/* Questionnaire.formItems997 */),
_1j0/* formItems777 */ = new T2(1,_1iZ/* Questionnaire.formItems996 */,_1iv/* Questionnaire.formItems778 */),
_1j1/* formItems776 */ = new T2(5,_1fj/* Questionnaire.formItems1028 */,_1j0/* Questionnaire.formItems777 */),
_1j2/* formItems775 */ = new T2(1,_1j1/* Questionnaire.formItems776 */,_k/* GHC.Types.[] */),
_1j3/* formItems774 */ = new T3(8,_1ir/* Questionnaire.formItems993 */,_Q0/* Questionnaire.formItems31 */,_1j2/* Questionnaire.formItems775 */),
_1j4/* formItems294 */ = new T2(1,_1j3/* Questionnaire.formItems774 */,_1fe/* Questionnaire.formItems295 */),
_1j5/* formItems293 */ = new T2(1,_17E/* Questionnaire.formItems1031 */,_1j4/* Questionnaire.formItems294 */),
_1j6/* formItems292 */ = new T2(1,_15X/* Questionnaire.formItems1136 */,_1j5/* Questionnaire.formItems293 */),
_1j7/* formItems291 */ = new T2(1,_13J/* Questionnaire.formItems1280 */,_1j6/* Questionnaire.formItems292 */),
_1j8/* formItems290 */ = new T2(1,_10o/* Questionnaire.formItems1498 */,_1j7/* Questionnaire.formItems291 */),
_1j9/* formItems289 */ = new T2(1,_YV/* Questionnaire.formItems1597 */,_1j8/* Questionnaire.formItems290 */),
_1ja/* formItems288 */ = new T2(1,_YG/* Questionnaire.formItems1612 */,_1j9/* Questionnaire.formItems289 */),
_1jb/* formItems287 */ = new T2(7,_YD/* Questionnaire.formItems1615 */,_1ja/* Questionnaire.formItems288 */),
_1jc/* formItems246 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is there a data integration tool that can handle and combine all the data types you are dealing with in your project?"));
}),
_1jd/* formItems245 */ = new T1(1,_1jc/* Questionnaire.formItems246 */),
_1je/* formItems244 */ = {_:0,a:_1jd/* Questionnaire.formItems245 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Xz/* Questionnaire.formItems61 */,h:_Xf/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1jf/* formItems243 */ = new T2(5,_1je/* Questionnaire.formItems244 */,_PW/* Questionnaire.formItems18 */),
_1jg/* formItems242 */ = new T2(1,_1jf/* Questionnaire.formItems243 */,_k/* GHC.Types.[] */),
_1jh/* formItems247 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Xz/* Questionnaire.formItems61 */,h:_Xf/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1ji/* formItems241 */ = new T3(8,_1jh/* Questionnaire.formItems247 */,_Q0/* Questionnaire.formItems31 */,_1jg/* Questionnaire.formItems242 */),
_1jj/* formItems240 */ = new T2(1,_1ji/* Questionnaire.formItems241 */,_k/* GHC.Types.[] */),
_1jk/* formItems253 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you have any non-equipment data capture?"));
}),
_1jl/* formItems252 */ = new T1(1,_1jk/* Questionnaire.formItems253 */),
_1jm/* formItems251 */ = {_:0,a:_1jl/* Questionnaire.formItems252 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Xz/* Questionnaire.formItems61 */,h:_Xz/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1jn/* formItems250 */ = new T2(5,_1jm/* Questionnaire.formItems251 */,_PW/* Questionnaire.formItems18 */),
_1jo/* formItems249 */ = new T2(1,_1jn/* Questionnaire.formItems250 */,_k/* GHC.Types.[] */),
_1jp/* formItems254 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Xz/* Questionnaire.formItems61 */,h:_Xz/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1jq/* formItems248 */ = new T3(8,_1jp/* Questionnaire.formItems254 */,_Q0/* Questionnaire.formItems31 */,_1jo/* Questionnaire.formItems249 */),
_1jr/* formItems239 */ = new T2(1,_1jq/* Questionnaire.formItems248 */,_1jj/* Questionnaire.formItems240 */),
_1js/* formItems260 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Where does the data come from? And who will need it? Sometimes the raw data is measured somewhere else than where the primary processing is taking place. In such cases the ingestion of the primary data may take special planning.</p>"));
}),
_1jt/* formItems259 */ = new T1(1,_1js/* Questionnaire.formItems260 */),
_1ju/* formItems262 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is special care needed to get the raw data ready for processing?"));
}),
_1jv/* formItems261 */ = new T1(1,_1ju/* Questionnaire.formItems262 */),
_1jw/* formItems258 */ = {_:0,a:_1jv/* Questionnaire.formItems261 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_1jt/* Questionnaire.formItems259 */,g:_Xz/* Questionnaire.formItems61 */,h:_XM/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1jx/* formItems257 */ = new T2(5,_1jw/* Questionnaire.formItems258 */,_PW/* Questionnaire.formItems18 */),
_1jy/* formItems256 */ = new T2(1,_1jx/* Questionnaire.formItems257 */,_k/* GHC.Types.[] */),
_1jz/* formItems263 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Xz/* Questionnaire.formItems61 */,h:_XM/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1jA/* formItems255 */ = new T3(8,_1jz/* Questionnaire.formItems263 */,_Q0/* Questionnaire.formItems31 */,_1jy/* Questionnaire.formItems256 */),
_1jB/* formItems238 */ = new T2(1,_1jA/* Questionnaire.formItems255 */,_1jr/* Questionnaire.formItems239 */),
_1jC/* formItems274 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("consider making them partner in the project"));
}),
_1jD/* formItems275 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Xz/* Questionnaire.formItems61 */,h:_PN/* Questionnaire.formItems86 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1jE/* formItems273 */ = new T2(4,_1jD/* Questionnaire.formItems275 */,_1jC/* Questionnaire.formItems274 */),
_1jF/* formItems272 */ = new T2(1,_1jE/* Questionnaire.formItems273 */,_k/* GHC.Types.[] */),
_1jG/* formItems271 */ = new T3(8,_1jD/* Questionnaire.formItems275 */,_Q0/* Questionnaire.formItems31 */,_1jF/* Questionnaire.formItems272 */),
_1jH/* formItems270 */ = new T2(1,_1jG/* Questionnaire.formItems271 */,_k/* GHC.Types.[] */),
_1jI/* formItems276 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External party"));
}),
_1jJ/* formItems269 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_1jI/* Questionnaire.formItems276 */,_1jH/* Questionnaire.formItems270 */),
_1jK/* formItems268 */ = new T2(1,_1jJ/* Questionnaire.formItems269 */,_k/* GHC.Types.[] */),
_1jL/* formItems278 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("In the project"));
}),
_1jM/* formItems277 */ = new T1(0,_1jL/* Questionnaire.formItems278 */),
_1jN/* formItems267 */ = new T2(1,_1jM/* Questionnaire.formItems277 */,_1jK/* Questionnaire.formItems268 */),
_1jO/* formItems281 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Are there easily accessible specialized service providers for data capture?</p>"));
}),
_1jP/* formItems280 */ = new T1(1,_1jO/* Questionnaire.formItems281 */),
_1jQ/* formItems283 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Who will do the measurements?"));
}),
_1jR/* formItems282 */ = new T1(1,_1jQ/* Questionnaire.formItems283 */),
_1jS/* formItems279 */ = {_:0,a:_1jR/* Questionnaire.formItems282 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_1jP/* Questionnaire.formItems280 */,g:_Xz/* Questionnaire.formItems61 */,h:_PN/* Questionnaire.formItems86 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1jT/* formItems266 */ = new T2(5,_1jS/* Questionnaire.formItems279 */,_1jN/* Questionnaire.formItems267 */),
_1jU/* formItems265 */ = new T2(1,_1jT/* Questionnaire.formItems266 */,_k/* GHC.Types.[] */),
_1jV/* formItems264 */ = new T3(8,_1jD/* Questionnaire.formItems275 */,_Q0/* Questionnaire.formItems31 */,_1jU/* Questionnaire.formItems265 */),
_1jW/* formItems237 */ = new T2(1,_1jV/* Questionnaire.formItems264 */,_1jB/* Questionnaire.formItems238 */),
_1jX/* formItems286 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data Capture/Measurement"));
}),
_1jY/* formItems285 */ = new T1(1,_1jX/* Questionnaire.formItems286 */),
_1jZ/* formItems284 */ = {_:0,a:_1jY/* Questionnaire.formItems285 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Xz/* Questionnaire.formItems61 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_1k0/* formItems236 */ = new T2(7,_1jZ/* Questionnaire.formItems284 */,_1jW/* Questionnaire.formItems237 */),
_1k1/* formItems201 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We have an alternative"));
}),
_1k2/* formItems200 */ = new T1(0,_1k1/* Questionnaire.formItems201 */),
_1k3/* formItems199 */ = new T2(1,_1k2/* Questionnaire.formItems200 */,_k/* GHC.Types.[] */),
_1k4/* formItems203 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Wait"));
}),
_1k5/* formItems202 */ = new T1(0,_1k4/* Questionnaire.formItems203 */),
_1k6/* formItems198 */ = new T2(1,_1k5/* Questionnaire.formItems202 */,_1k3/* Questionnaire.formItems199 */),
_1k7/* formItems206 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">What will you do if the compute facility is down?</p>"));
}),
_1k8/* formItems205 */ = new T1(1,_1k7/* Questionnaire.formItems206 */),
_1k9/* formItems208 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you have a contingency plan?"));
}),
_1ka/* formItems207 */ = new T1(1,_1k9/* Questionnaire.formItems208 */),
_1kb/* formItems204 */ = {_:0,a:_1ka/* Questionnaire.formItems207 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_1k8/* Questionnaire.formItems205 */,g:_Xf/* Questionnaire.formItems52 */,h:_Xf/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1kc/* formItems197 */ = new T2(5,_1kb/* Questionnaire.formItems204 */,_1k6/* Questionnaire.formItems198 */),
_1kd/* formItems196 */ = new T2(1,_1kc/* Questionnaire.formItems197 */,_k/* GHC.Types.[] */),
_1ke/* formItems209 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Xf/* Questionnaire.formItems52 */,h:_Xf/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1kf/* formItems195 */ = new T3(8,_1ke/* Questionnaire.formItems209 */,_Q0/* Questionnaire.formItems31 */,_1kd/* Questionnaire.formItems196 */),
_1kg/* formItems194 */ = new T2(1,_1kf/* Questionnaire.formItems195 */,_k/* GHC.Types.[] */),
_1kh/* formItems111 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Drill deeper"));
}),
_1ki/* formItems110 */ = new T1(0,_1kh/* Questionnaire.formItems111 */),
_1kj/* formItems109 */ = new T2(1,_1ki/* Questionnaire.formItems110 */,_k/* GHC.Types.[] */),
_1kk/* formItems113 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Taken care of"));
}),
_1kl/* formItems112 */ = new T1(0,_1kk/* Questionnaire.formItems113 */),
_1km/* formItems108 */ = new T2(1,_1kl/* Questionnaire.formItems112 */,_1kj/* Questionnaire.formItems109 */),
_1kn/* formItems215 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you validate the integrity of the results?"));
}),
_1ko/* formItems214 */ = new T1(1,_1kn/* Questionnaire.formItems215 */),
_1kp/* formItems213 */ = {_:0,a:_1ko/* Questionnaire.formItems214 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Xf/* Questionnaire.formItems52 */,h:_Xz/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1kq/* formItems212 */ = new T2(5,_1kp/* Questionnaire.formItems213 */,_1km/* Questionnaire.formItems108 */),
_1kr/* formItems211 */ = new T2(1,_1kq/* Questionnaire.formItems212 */,_k/* GHC.Types.[] */),
_1ks/* formItems216 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Xf/* Questionnaire.formItems52 */,h:_Xz/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1kt/* formItems210 */ = new T3(8,_1ks/* Questionnaire.formItems216 */,_Q0/* Questionnaire.formItems31 */,_1kr/* Questionnaire.formItems211 */),
_1ku/* formItems193 */ = new T2(1,_1kt/* Questionnaire.formItems210 */,_1kg/* Questionnaire.formItems194 */),
_1kv/* formItems222 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you make sure to know what exactly has been run?"));
}),
_1kw/* formItems221 */ = new T1(1,_1kv/* Questionnaire.formItems222 */),
_1kx/* formItems220 */ = {_:0,a:_1kw/* Questionnaire.formItems221 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Xf/* Questionnaire.formItems52 */,h:_XM/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1ky/* formItems219 */ = new T2(5,_1kx/* Questionnaire.formItems220 */,_1km/* Questionnaire.formItems108 */),
_1kz/* formItems218 */ = new T2(1,_1ky/* Questionnaire.formItems219 */,_k/* GHC.Types.[] */),
_1kA/* formItems223 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Xf/* Questionnaire.formItems52 */,h:_XM/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1kB/* formItems217 */ = new T3(8,_1kA/* Questionnaire.formItems223 */,_Q0/* Questionnaire.formItems31 */,_1kz/* Questionnaire.formItems218 */),
_1kC/* formItems192 */ = new T2(1,_1kB/* Questionnaire.formItems217 */,_1ku/* Questionnaire.formItems193 */),
_1kD/* formItems229 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">It is likely that you will be developing or modifying the workflow for data processing. There are a lot of aspects of this workflow that can play a role in your data management, such as the use of an existing work flow engine, the use of existing software vs development of new components, and whether every run needs human intervention or whether all data processing can be run in bulk once the work flow has been defined.</p>"));
}),
_1kE/* formItems228 */ = new T1(1,_1kD/* Questionnaire.formItems229 */),
_1kF/* formItems231 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Workflow development"));
}),
_1kG/* formItems230 */ = new T1(1,_1kF/* Questionnaire.formItems231 */),
_1kH/* formItems227 */ = {_:0,a:_1kG/* Questionnaire.formItems230 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_1kE/* Questionnaire.formItems228 */,g:_Xf/* Questionnaire.formItems52 */,h:_PN/* Questionnaire.formItems86 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1kI/* formItems226 */ = new T2(5,_1kH/* Questionnaire.formItems227 */,_1km/* Questionnaire.formItems108 */),
_1kJ/* formItems225 */ = new T2(1,_1kI/* Questionnaire.formItems226 */,_k/* GHC.Types.[] */),
_1kK/* formItems232 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Xf/* Questionnaire.formItems52 */,h:_PN/* Questionnaire.formItems86 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1kL/* formItems224 */ = new T3(8,_1kK/* Questionnaire.formItems232 */,_Q0/* Questionnaire.formItems31 */,_1kJ/* Questionnaire.formItems225 */),
_1kM/* formItems191 */ = new T2(1,_1kL/* Questionnaire.formItems224 */,_1kC/* Questionnaire.formItems192 */),
_1kN/* formItems235 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data processing and curation"));
}),
_1kO/* formItems234 */ = new T1(1,_1kN/* Questionnaire.formItems235 */),
_1kP/* formItems233 */ = {_:0,a:_1kO/* Questionnaire.formItems234 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_Xf/* Questionnaire.formItems52 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_1kQ/* formItems190 */ = new T2(7,_1kP/* Questionnaire.formItems233 */,_1kM/* Questionnaire.formItems191 */),
_1kR/* formItems149 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you have all tools to couple the necessary data types?"));
}),
_1kS/* formItems148 */ = new T1(1,_1kR/* Questionnaire.formItems149 */),
_1kT/* formItems147 */ = {_:0,a:_1kS/* Questionnaire.formItems148 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_X6/* Questionnaire.formItems43 */,h:_X6/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1kU/* formItems146 */ = new T2(5,_1kT/* Questionnaire.formItems147 */,_PW/* Questionnaire.formItems18 */),
_1kV/* formItems145 */ = new T2(1,_1kU/* Questionnaire.formItems146 */,_k/* GHC.Types.[] */),
_1kW/* formItems150 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_X6/* Questionnaire.formItems43 */,h:_X6/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1kX/* formItems144 */ = new T3(8,_1kW/* Questionnaire.formItems150 */,_Q0/* Questionnaire.formItems31 */,_1kV/* Questionnaire.formItems145 */),
_1kY/* formItems143 */ = new T2(1,_1kX/* Questionnaire.formItems144 */,_k/* GHC.Types.[] */),
_1kZ/* formItems156 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will there be potential issues with statistical normalization?"));
}),
_1l0/* formItems155 */ = new T1(1,_1kZ/* Questionnaire.formItems156 */),
_1l1/* formItems154 */ = {_:0,a:_1l0/* Questionnaire.formItems155 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_X6/* Questionnaire.formItems43 */,h:_Xf/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1l2/* formItems153 */ = new T2(5,_1l1/* Questionnaire.formItems154 */,_PW/* Questionnaire.formItems18 */),
_1l3/* formItems152 */ = new T2(1,_1l2/* Questionnaire.formItems153 */,_k/* GHC.Types.[] */),
_1l4/* formItems157 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_X6/* Questionnaire.formItems43 */,h:_Xf/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1l5/* formItems151 */ = new T3(8,_1l4/* Questionnaire.formItems157 */,_Q0/* Questionnaire.formItems31 */,_1l3/* Questionnaire.formItems152 */),
_1l6/* formItems142 */ = new T2(1,_1l5/* Questionnaire.formItems151 */,_1kY/* Questionnaire.formItems143 */),
_1l7/* formItems168 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Choose the ontologies before you start"));
}),
_1l8/* formItems169 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_X6/* Questionnaire.formItems43 */,h:_Xz/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1l9/* formItems167 */ = new T2(4,_1l8/* Questionnaire.formItems169 */,_1l7/* Questionnaire.formItems168 */),
_1la/* formItems166 */ = new T2(1,_1l9/* Questionnaire.formItems167 */,_k/* GHC.Types.[] */),
_1lb/* formItems165 */ = new T3(8,_1l8/* Questionnaire.formItems169 */,_Q0/* Questionnaire.formItems31 */,_1la/* Questionnaire.formItems166 */),
_1lc/* formItems164 */ = new T2(1,_1lb/* Questionnaire.formItems165 */,_k/* GHC.Types.[] */),
_1ld/* formItems163 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_1lc/* Questionnaire.formItems164 */),
_1le/* formItems162 */ = new T2(1,_1ld/* Questionnaire.formItems163 */,_k/* GHC.Types.[] */),
_1lf/* formItems161 */ = new T2(1,_PV/* Questionnaire.formItems22 */,_1le/* Questionnaire.formItems162 */),
_1lg/* formItems172 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be using common ontologies?"));
}),
_1lh/* formItems171 */ = new T1(1,_1lg/* Questionnaire.formItems172 */),
_1li/* formItems170 */ = {_:0,a:_1lh/* Questionnaire.formItems171 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_X6/* Questionnaire.formItems43 */,h:_Xz/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1lj/* formItems160 */ = new T2(5,_1li/* Questionnaire.formItems170 */,_1lf/* Questionnaire.formItems161 */),
_1lk/* formItems159 */ = new T2(1,_1lj/* Questionnaire.formItems160 */,_k/* GHC.Types.[] */),
_1ll/* formItems158 */ = new T3(8,_1l8/* Questionnaire.formItems169 */,_Q0/* Questionnaire.formItems31 */,_1lk/* Questionnaire.formItems159 */),
_1lm/* formItems141 */ = new T2(1,_1ll/* Questionnaire.formItems158 */,_1l6/* Questionnaire.formItems142 */),
_1ln/* formItems178 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be using common or exchangeable units?"));
}),
_1lo/* formItems177 */ = new T1(1,_1ln/* Questionnaire.formItems178 */),
_1lp/* formItems176 */ = {_:0,a:_1lo/* Questionnaire.formItems177 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_X6/* Questionnaire.formItems43 */,h:_XM/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1lq/* formItems175 */ = new T2(5,_1lp/* Questionnaire.formItems176 */,_PW/* Questionnaire.formItems18 */),
_1lr/* formItems174 */ = new T2(1,_1lq/* Questionnaire.formItems175 */,_k/* GHC.Types.[] */),
_1ls/* formItems179 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_X6/* Questionnaire.formItems43 */,h:_XM/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1lt/* formItems173 */ = new T3(8,_1ls/* Questionnaire.formItems179 */,_Q0/* Questionnaire.formItems31 */,_1lr/* Questionnaire.formItems174 */),
_1lu/* formItems140 */ = new T2(1,_1lt/* Questionnaire.formItems173 */,_1lm/* Questionnaire.formItems141 */),
_1lv/* formItems185 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("What is the framework you will use for data integration?"));
}),
_1lw/* formItems184 */ = new T1(1,_1lv/* Questionnaire.formItems185 */),
_1lx/* formItems183 */ = {_:0,a:_1lw/* Questionnaire.formItems184 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_X6/* Questionnaire.formItems43 */,h:_PN/* Questionnaire.formItems86 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1ly/* formItems182 */ = new T2(5,_1lx/* Questionnaire.formItems183 */,_1km/* Questionnaire.formItems108 */),
_1lz/* formItems181 */ = new T2(1,_1ly/* Questionnaire.formItems182 */,_k/* GHC.Types.[] */),
_1lA/* formItems186 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_X6/* Questionnaire.formItems43 */,h:_PN/* Questionnaire.formItems86 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1lB/* formItems180 */ = new T3(8,_1lA/* Questionnaire.formItems186 */,_Q0/* Questionnaire.formItems31 */,_1lz/* Questionnaire.formItems181 */),
_1lC/* formItems139 */ = new T2(1,_1lB/* Questionnaire.formItems180 */,_1lu/* Questionnaire.formItems140 */),
_1lD/* formItems189 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data integration"));
}),
_1lE/* formItems188 */ = new T1(1,_1lD/* Questionnaire.formItems189 */),
_1lF/* formItems187 */ = {_:0,a:_1lE/* Questionnaire.formItems188 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_X6/* Questionnaire.formItems43 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_1lG/* formItems138 */ = new T2(7,_1lF/* Questionnaire.formItems187 */,_1lC/* Questionnaire.formItems139 */),
_1lH/* formItems30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be archiving data?"));
}),
_1lI/* formItems29 */ = new T1(1,_1lH/* Questionnaire.formItems30 */),
_1lJ/* formItems24 */ = {_:0,a:_1lI/* Questionnaire.formItems29 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WD/* Questionnaire.formItems27 */,h:_WL/* Questionnaire.formItems25 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1lK/* formItems17 */ = new T2(5,_1lJ/* Questionnaire.formItems24 */,_PW/* Questionnaire.formItems18 */),
_1lL/* formItems16 */ = new T2(1,_1lK/* Questionnaire.formItems17 */,_k/* GHC.Types.[] */),
_1lM/* formItems32 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WD/* Questionnaire.formItems27 */,h:_WL/* Questionnaire.formItems25 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1lN/* formItems15 */ = new T3(8,_1lM/* Questionnaire.formItems32 */,_Q0/* Questionnaire.formItems31 */,_1lL/* Questionnaire.formItems16 */),
_1lO/* formItems14 */ = new T2(1,_1lN/* Questionnaire.formItems15 */,_k/* GHC.Types.[] */),
_1lP/* formItems39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Drill Deeper"));
}),
_1lQ/* formItems38 */ = new T1(0,_1lP/* Questionnaire.formItems39 */),
_1lR/* formItems37 */ = new T2(1,_1lQ/* Questionnaire.formItems38 */,_k/* GHC.Types.[] */),
_1lS/* formItems36 */ = new T2(1,_11e/* Questionnaire.formItems40 */,_1lR/* Questionnaire.formItems37 */),
_1lT/* formItems46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Did you work out the financial aspects of making the data available?"));
}),
_1lU/* formItems45 */ = new T1(1,_1lT/* Questionnaire.formItems46 */),
_1lV/* formItems42 */ = {_:0,a:_1lU/* Questionnaire.formItems45 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WD/* Questionnaire.formItems27 */,h:_X6/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1lW/* formItems35 */ = new T2(5,_1lV/* Questionnaire.formItems42 */,_1lS/* Questionnaire.formItems36 */),
_1lX/* formItems34 */ = new T2(1,_1lW/* Questionnaire.formItems35 */,_k/* GHC.Types.[] */),
_1lY/* formItems47 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WD/* Questionnaire.formItems27 */,h:_X6/* Questionnaire.formItems43 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1lZ/* formItems33 */ = new T3(8,_1lY/* Questionnaire.formItems47 */,_Q0/* Questionnaire.formItems31 */,_1lX/* Questionnaire.formItems34 */),
_1m0/* formItems13 */ = new T2(1,_1lZ/* Questionnaire.formItems33 */,_1lO/* Questionnaire.formItems14 */),
_1m1/* formItems55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Where will you make your data available?"));
}),
_1m2/* formItems54 */ = new T1(1,_1m1/* Questionnaire.formItems55 */),
_1m3/* formItems51 */ = {_:0,a:_1m2/* Questionnaire.formItems54 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WD/* Questionnaire.formItems27 */,h:_Xf/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1m4/* formItems50 */ = new T2(5,_1m3/* Questionnaire.formItems51 */,_1lS/* Questionnaire.formItems36 */),
_1m5/* formItems49 */ = new T2(1,_1m4/* Questionnaire.formItems50 */,_k/* GHC.Types.[] */),
_1m6/* formItems56 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WD/* Questionnaire.formItems27 */,h:_Xf/* Questionnaire.formItems52 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1m7/* formItems48 */ = new T3(8,_1m6/* Questionnaire.formItems56 */,_Q0/* Questionnaire.formItems31 */,_1m5/* Questionnaire.formItems49 */),
_1m8/* formItems12 */ = new T2(1,_1m7/* Questionnaire.formItems48 */,_1m0/* Questionnaire.formItems13 */),
_1m9/* formItems64 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" Are there business reasons why (some of your) data can not be completely open?"));
}),
_1ma/* formItems63 */ = new T1(1,_1m9/* Questionnaire.formItems64 */),
_1mb/* formItems60 */ = {_:0,a:_1ma/* Questionnaire.formItems63 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WD/* Questionnaire.formItems27 */,h:_Xz/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1mc/* formItems59 */ = new T2(5,_1mb/* Questionnaire.formItems60 */,_PW/* Questionnaire.formItems18 */),
_1md/* formItems58 */ = new T2(1,_1mc/* Questionnaire.formItems59 */,_k/* GHC.Types.[] */),
_1me/* formItems65 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WD/* Questionnaire.formItems27 */,h:_Xz/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1mf/* formItems57 */ = new T3(8,_1me/* Questionnaire.formItems65 */,_Q0/* Questionnaire.formItems31 */,_1md/* Questionnaire.formItems58 */),
_1mg/* formItems11 */ = new T2(1,_1mf/* Questionnaire.formItems57 */,_1m8/* Questionnaire.formItems12 */),
_1mh/* formItems73 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" Are there legal reasons why (some of your) data can not be completely open?"));
}),
_1mi/* formItems72 */ = new T1(1,_1mh/* Questionnaire.formItems73 */),
_1mj/* formItems69 */ = {_:0,a:_1mi/* Questionnaire.formItems72 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WD/* Questionnaire.formItems27 */,h:_XM/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1mk/* formItems68 */ = new T2(5,_1mj/* Questionnaire.formItems69 */,_PW/* Questionnaire.formItems18 */),
_1ml/* formItems67 */ = new T2(1,_1mk/* Questionnaire.formItems68 */,_k/* GHC.Types.[] */),
_1mm/* formItems74 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WD/* Questionnaire.formItems27 */,h:_XM/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1mn/* formItems66 */ = new T3(8,_1mm/* Questionnaire.formItems74 */,_Q0/* Questionnaire.formItems31 */,_1ml/* Questionnaire.formItems67 */),
_1mo/* formItems10 */ = new T2(1,_1mn/* Questionnaire.formItems66 */,_1mg/* Questionnaire.formItems11 */),
_1mp/* formItems84 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("You will need to explain!"));
}),
_1mq/* formItems85 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WD/* Questionnaire.formItems27 */,h:_PN/* Questionnaire.formItems86 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1mr/* formItems83 */ = new T2(4,_1mq/* Questionnaire.formItems85 */,_1mp/* Questionnaire.formItems84 */),
_1ms/* formItems82 */ = new T2(1,_1mr/* Questionnaire.formItems83 */,_k/* GHC.Types.[] */),
_1mt/* formItems81 */ = new T3(8,_1mq/* Questionnaire.formItems85 */,_Q0/* Questionnaire.formItems31 */,_1ms/* Questionnaire.formItems82 */),
_1mu/* formItems80 */ = new T2(1,_1mt/* Questionnaire.formItems81 */,_k/* GHC.Types.[] */),
_1mv/* formItems79 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PU/* Questionnaire.formItems23 */,_1mu/* Questionnaire.formItems80 */),
_1mw/* formItems78 */ = new T2(1,_1mv/* Questionnaire.formItems79 */,_PT/* Questionnaire.formItems19 */),
_1mx/* formItems90 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be working with the philosophy \'as open as possible\' for your data?"));
}),
_1my/* formItems89 */ = new T1(1,_1mx/* Questionnaire.formItems90 */),
_1mz/* formItems88 */ = {_:0,a:_1my/* Questionnaire.formItems89 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WD/* Questionnaire.formItems27 */,h:_PN/* Questionnaire.formItems86 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1mA/* formItems77 */ = new T2(5,_1mz/* Questionnaire.formItems88 */,_1mw/* Questionnaire.formItems78 */),
_1mB/* formItems76 */ = new T2(1,_1mA/* Questionnaire.formItems77 */,_k/* GHC.Types.[] */),
_1mC/* formItems75 */ = new T3(8,_1mq/* Questionnaire.formItems85 */,_Q0/* Questionnaire.formItems31 */,_1mB/* Questionnaire.formItems76 */),
_1mD/* formItems9 */ = new T2(1,_1mC/* Questionnaire.formItems75 */,_1mo/* Questionnaire.formItems10 */),
_1mE/* formItems93 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Information and insight"));
}),
_1mF/* formItems92 */ = new T1(1,_1mE/* Questionnaire.formItems93 */),
_1mG/* formItems91 */ = {_:0,a:_1mF/* Questionnaire.formItems92 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WD/* Questionnaire.formItems27 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_1mH/* formItems8 */ = new T2(7,_1mG/* Questionnaire.formItems91 */,_1mD/* Questionnaire.formItems9 */),
_1mI/* formItems7 */ = new T2(1,_1mH/* Questionnaire.formItems8 */,_k/* GHC.Types.[] */),
_1mJ/* formItems137 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data interpretation"));
}),
_1mK/* formItems136 */ = new T1(1,_1mJ/* Questionnaire.formItems137 */),
_1mL/* formItems135 */ = {_:0,a:_1mK/* Questionnaire.formItems136 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WL/* Questionnaire.formItems25 */,h:_4y/* GHC.Base.Nothing */,i:_4y/* GHC.Base.Nothing */,j:_4x/* GHC.Types.False */,k:_k/* GHC.Types.[] */},
_1mM/* formItems130 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Make sure this has been taken into account in the capacity planning under \'Data design and planning\'"));
}),
_1mN/* formItems131 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WL/* Questionnaire.formItems25 */,h:_PN/* Questionnaire.formItems86 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1mO/* formItems129 */ = new T2(4,_1mN/* Questionnaire.formItems131 */,_1mM/* Questionnaire.formItems130 */),
_1mP/* formItems128 */ = new T2(1,_1mO/* Questionnaire.formItems129 */,_k/* GHC.Types.[] */),
_1mQ/* formItems127 */ = new T3(8,_1mN/* Questionnaire.formItems131 */,_Q0/* Questionnaire.formItems31 */,_1mP/* Questionnaire.formItems128 */),
_1mR/* formItems126 */ = new T2(1,_1mQ/* Questionnaire.formItems127 */,_k/* GHC.Types.[] */),
_1mS/* formItems125 */ = new T3(1,_PJ/* FormEngine.FormItem.NoNumbering */,_PR/* Questionnaire.formItems21 */,_1mR/* Questionnaire.formItems126 */),
_1mT/* formItems124 */ = new T2(1,_1mS/* Questionnaire.formItems125 */,_k/* GHC.Types.[] */),
_1mU/* formItems123 */ = new T2(1,_1kl/* Questionnaire.formItems112 */,_1mT/* Questionnaire.formItems124 */),
_1mV/* formItems134 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will data interpretation and modeling require significant compute infrastructure capacity?"));
}),
_1mW/* formItems133 */ = new T1(1,_1mV/* Questionnaire.formItems134 */),
_1mX/* formItems132 */ = {_:0,a:_1mW/* Questionnaire.formItems133 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WL/* Questionnaire.formItems25 */,h:_PN/* Questionnaire.formItems86 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1mY/* formItems122 */ = new T2(5,_1mX/* Questionnaire.formItems132 */,_1mU/* Questionnaire.formItems123 */),
_1mZ/* formItems121 */ = new T2(1,_1mY/* Questionnaire.formItems122 */,_k/* GHC.Types.[] */),
_1n0/* formItems120 */ = new T3(8,_1mN/* Questionnaire.formItems131 */,_Q0/* Questionnaire.formItems31 */,_1mZ/* Questionnaire.formItems121 */),
_1n1/* formItems116 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\"question-description\">Data analysis is normally done manually on a step-by-step basis. It is essential to make sure all steps are properly documented, otherwise results will not be reproducible.</p>"));
}),
_1n2/* formItems115 */ = new T1(1,_1n1/* Questionnaire.formItems116 */),
_1n3/* formItems118 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How will you be making sure there is good provenance of the data analysis?"));
}),
_1n4/* formItems117 */ = new T1(1,_1n3/* Questionnaire.formItems118 */),
_1n5/* formItems114 */ = {_:0,a:_1n4/* Questionnaire.formItems117 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_1n2/* Questionnaire.formItems115 */,g:_WL/* Questionnaire.formItems25 */,h:_XM/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1n6/* formItems107 */ = new T2(5,_1n5/* Questionnaire.formItems114 */,_1km/* Questionnaire.formItems108 */),
_1n7/* formItems106 */ = new T2(1,_1n6/* Questionnaire.formItems107 */,_k/* GHC.Types.[] */),
_1n8/* formItems119 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WL/* Questionnaire.formItems25 */,h:_XM/* Questionnaire.formItems70 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1n9/* formItems105 */ = new T3(8,_1n8/* Questionnaire.formItems119 */,_Q0/* Questionnaire.formItems31 */,_1n7/* Questionnaire.formItems106 */),
_1na/* formItems104 */ = {_:0,a:_4y/* GHC.Base.Nothing */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WL/* Questionnaire.formItems25 */,h:_Xz/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1nb/* formItems103 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Will you be doing (automated) knowledge discovery?"));
}),
_1nc/* formItems102 */ = new T1(1,_1nb/* Questionnaire.formItems103 */),
_1nd/* formItems101 */ = {_:0,a:_1nc/* Questionnaire.formItems102 */,b:_PJ/* FormEngine.FormItem.NoNumbering */,c:_4y/* GHC.Base.Nothing */,d:_k/* GHC.Types.[] */,e:_4y/* GHC.Base.Nothing */,f:_4y/* GHC.Base.Nothing */,g:_WL/* Questionnaire.formItems25 */,h:_Xz/* Questionnaire.formItems61 */,i:_4y/* GHC.Base.Nothing */,j:_8G/* GHC.Types.True */,k:_k/* GHC.Types.[] */},
_1ne/* formItems100 */ = new T2(5,_1nd/* Questionnaire.formItems101 */,_PW/* Questionnaire.formItems18 */),
_1nf/* formItems99 */ = new T2(1,_1ne/* Questionnaire.formItems100 */,_k/* GHC.Types.[] */),
_1ng/* formItems98 */ = new T3(8,_1na/* Questionnaire.formItems104 */,_Q0/* Questionnaire.formItems31 */,_1nf/* Questionnaire.formItems99 */),
_1nh/* formItems97 */ = new T2(1,_1ng/* Questionnaire.formItems98 */,_k/* GHC.Types.[] */),
_1ni/* formItems96 */ = new T2(1,_1n9/* Questionnaire.formItems105 */,_1nh/* Questionnaire.formItems97 */),
_1nj/* formItems95 */ = new T2(1,_1n0/* Questionnaire.formItems120 */,_1ni/* Questionnaire.formItems96 */),
_1nk/* formItems94 */ = new T2(7,_1mL/* Questionnaire.formItems135 */,_1nj/* Questionnaire.formItems95 */),
_1nl/* formItems6 */ = new T2(1,_1nk/* Questionnaire.formItems94 */,_1mI/* Questionnaire.formItems7 */),
_1nm/* formItems5 */ = new T2(1,_1lG/* Questionnaire.formItems138 */,_1nl/* Questionnaire.formItems6 */),
_1nn/* formItems4 */ = new T2(1,_1kQ/* Questionnaire.formItems190 */,_1nm/* Questionnaire.formItems5 */),
_1no/* formItems3 */ = new T2(1,_1k0/* Questionnaire.formItems236 */,_1nn/* Questionnaire.formItems4 */),
_1np/* formItems2 */ = new T2(1,_1jb/* Questionnaire.formItems287 */,_1no/* Questionnaire.formItems3 */),
_1nq/* formItems1 */ = new T2(1,_YA/* Questionnaire.formItems1618 */,_1np/* Questionnaire.formItems2 */),
_1nr/* prepareForm_xs */ = new T(function(){
  return new T2(1,_51/* FormEngine.FormItem.$fShowNumbering2 */,_1nr/* FormEngine.FormItem.prepareForm_xs */);
}),
_1ns/* prepareForm1 */ = new T2(1,_1nr/* FormEngine.FormItem.prepareForm_xs */,_51/* FormEngine.FormItem.$fShowNumbering2 */),
_1nt/* formItems */ = new T(function(){
  return E(B(_Py/* FormEngine.FormItem.$wgo1 */(_1nq/* Questionnaire.formItems1 */, _1ns/* FormEngine.FormItem.prepareForm1 */, _k/* GHC.Types.[] */)).b);
}),
_1nu/* lookup */ = function(_1nv/* s9uF */, _1nw/* s9uG */, _1nx/* s9uH */){
  while(1){
    var _1ny/* s9uI */ = E(_1nx/* s9uH */);
    if(!_1ny/* s9uI */._){
      return __Z/* EXTERNAL */;
    }else{
      var _1nz/* s9uL */ = E(_1ny/* s9uI */.a);
      if(!B(A3(_eo/* GHC.Classes.== */,_1nv/* s9uF */, _1nw/* s9uG */, _1nz/* s9uL */.a))){
        _1nx/* s9uH */ = _1ny/* s9uI */.b;
        continue;
      }else{
        return new T1(1,_1nz/* s9uL */.b);
      }
    }
  }
},
_1nA/* getMaybeNumberFIUnitValue */ = function(_1nB/* s9J8 */, _1nC/* s9J9 */){
  var _1nD/* s9Ja */ = E(_1nC/* s9J9 */);
  if(!_1nD/* s9Ja */._){
    return __Z/* EXTERNAL */;
  }else{
    var _1nE/* s9Jc */ = E(_1nB/* s9J8 */);
    if(_1nE/* s9Jc */._==3){
      var _1nF/* s9Jg */ = E(_1nE/* s9Jc */.b);
      switch(_1nF/* s9Jg */._){
        case 0:
          return new T1(1,_1nF/* s9Jg */.a);
        case 1:
          return new F(function(){return _1nu/* GHC.List.lookup */(_aM/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_7/* GHC.Base.++ */(B(_27/* FormEngine.FormItem.numbering2text */(E(_1nE/* s9Jc */.a).b)), _8k/* FormEngine.FormItem.nfiUnitId1 */));
          }), _1nD/* s9Ja */.a);});
          break;
        default:
          return __Z/* EXTERNAL */;
      }
    }else{
      return E(_qZ/* FormEngine.FormItem.nfiUnit1 */);
    }
  }
},
_1nG/* fiId */ = function(_1nH/* s5jZ */){
  return new F(function(){return _27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_1nH/* s5jZ */)).b);});
},
_1nI/* isCheckboxChecked1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("on"));
}),
_1nJ/* isCheckboxChecked */ = function(_1nK/* s9J1 */, _1nL/* s9J2 */){
  var _1nM/* s9J3 */ = E(_1nL/* s9J2 */);
  if(!_1nM/* s9J3 */._){
    return false;
  }else{
    var _1nN/* s9J6 */ = B(_1nu/* GHC.List.lookup */(_aM/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
      return B(_1nG/* FormEngine.FormItem.fiId */(_1nK/* s9J1 */));
    }), _1nM/* s9J3 */.a));
    if(!_1nN/* s9J6 */._){
      return false;
    }else{
      return new F(function(){return _2n/* GHC.Base.eqString */(_1nN/* s9J6 */.a, _1nI/* FormEngine.FormData.isCheckboxChecked1 */);});
    }
  }
},
_1nO/* isOptionSelected */ = function(_1nP/* s9Ix */, _1nQ/* s9Iy */, _1nR/* s9Iz */){
  var _1nS/* s9IA */ = E(_1nR/* s9Iz */);
  if(!_1nS/* s9IA */._){
    return false;
  }else{
    var _1nT/* s9IP */ = B(_1nu/* GHC.List.lookup */(_aM/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
      return B(_27/* FormEngine.FormItem.numbering2text */(B(_1A/* FormEngine.FormItem.fiDescriptor */(_1nQ/* s9Iy */)).b));
    }), _1nS/* s9IA */.a));
    if(!_1nT/* s9IP */._){
      return false;
    }else{
      var _1nU/* s9IQ */ = _1nT/* s9IP */.a,
      _1nV/* s9IR */ = E(_1nP/* s9Ix */);
      if(!_1nV/* s9IR */._){
        return new F(function(){return _2n/* GHC.Base.eqString */(_1nU/* s9IQ */, _1nV/* s9IR */.a);});
      }else{
        return new F(function(){return _2n/* GHC.Base.eqString */(_1nU/* s9IQ */, _1nV/* s9IR */.b);});
      }
    }
  }
},
_1nW/* mapMaybe */ = function(_1nX/*  s7rs */, _1nY/*  s7rt */){
  while(1){
    var _1nZ/*  mapMaybe */ = B((function(_1o0/* s7rs */, _1o1/* s7rt */){
      var _1o2/* s7ru */ = E(_1o1/* s7rt */);
      if(!_1o2/* s7ru */._){
        return __Z/* EXTERNAL */;
      }else{
        var _1o3/* s7rw */ = _1o2/* s7ru */.b,
        _1o4/* s7rx */ = B(A1(_1o0/* s7rs */,_1o2/* s7ru */.a));
        if(!_1o4/* s7rx */._){
          var _1o5/*   s7rs */ = _1o0/* s7rs */;
          _1nX/*  s7rs */ = _1o5/*   s7rs */;
          _1nY/*  s7rt */ = _1o3/* s7rw */;
          return __continue/* EXTERNAL */;
        }else{
          return new T2(1,_1o4/* s7rx */.a,new T(function(){
            return B(_1nW/* Data.Maybe.mapMaybe */(_1o0/* s7rs */, _1o3/* s7rw */));
          }));
        }
      }
    })(_1nX/*  s7rs */, _1nY/*  s7rt */));
    if(_1nZ/*  mapMaybe */!=__continue/* EXTERNAL */){
      return _1nZ/*  mapMaybe */;
    }
  }
},
_1o6/* maybeStr2maybeInt2 */ = new T(function(){
  return B(A3(_mn/* GHC.Read.$fReadInt3 */,_mQ/* GHC.Read.$fReadInt_$sconvertInt */, _lS/* Text.ParserCombinators.ReadPrec.minPrec */, _aZ/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
}),
_1o7/* maybeStr2maybeInt1 */ = function(_1o8/* scgM */){
  var _1o9/* scgN */ = B(_8s/* Text.ParserCombinators.ReadP.run */(_1o6/* FormEngine.FormElement.FormElement.maybeStr2maybeInt2 */, _1o8/* scgM */));
  return (_1o9/* scgN */._==0) ? __Z/* EXTERNAL */ : (E(_1o9/* scgN */.b)._==0) ? new T1(1,E(_1o9/* scgN */.a).a) : __Z/* EXTERNAL */;
},
_1oa/* makeElem */ = function(_1ob/* scgZ */, _1oc/* sch0 */, _1od/* sch1 */){
  var _1oe/* sch2 */ = E(_1od/* sch1 */);
  switch(_1oe/* sch2 */._){
    case 0:
      var _1of/* schl */ = new T(function(){
        var _1og/* sch4 */ = E(_1oc/* sch0 */);
        if(!_1og/* sch4 */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1oh/* schj */ = B(_1nu/* GHC.List.lookup */(_aM/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_27/* FormEngine.FormItem.numbering2text */(E(_1oe/* sch2 */.a).b));
          }), _1og/* sch4 */.a));
          if(!_1oh/* schj */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_1oh/* schj */.a);
          }
        }
      });
      return new T1(1,new T3(1,_1oe/* sch2 */,_1of/* schl */,_1ob/* scgZ */));
    case 1:
      var _1oi/* schF */ = new T(function(){
        var _1oj/* scho */ = E(_1oc/* sch0 */);
        if(!_1oj/* scho */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1ok/* schD */ = B(_1nu/* GHC.List.lookup */(_aM/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_27/* FormEngine.FormItem.numbering2text */(E(_1oe/* sch2 */.a).b));
          }), _1oj/* scho */.a));
          if(!_1ok/* schD */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_1ok/* schD */.a);
          }
        }
      });
      return new T1(1,new T3(2,_1oe/* sch2 */,_1oi/* schF */,_1ob/* scgZ */));
    case 2:
      var _1ol/* schZ */ = new T(function(){
        var _1om/* schI */ = E(_1oc/* sch0 */);
        if(!_1om/* schI */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1on/* schX */ = B(_1nu/* GHC.List.lookup */(_aM/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_27/* FormEngine.FormItem.numbering2text */(E(_1oe/* sch2 */.a).b));
          }), _1om/* schI */.a));
          if(!_1on/* schX */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_1on/* schX */.a);
          }
        }
      });
      return new T1(1,new T3(3,_1oe/* sch2 */,_1ol/* schZ */,_1ob/* scgZ */));
    case 3:
      var _1oo/* scik */ = new T(function(){
        var _1op/* sci3 */ = E(_1oc/* sch0 */);
        if(!_1op/* sci3 */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1oq/* scii */ = B(_1nu/* GHC.List.lookup */(_aM/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_27/* FormEngine.FormItem.numbering2text */(E(_1oe/* sch2 */.a).b));
          }), _1op/* sci3 */.a));
          if(!_1oq/* scii */._){
            return __Z/* EXTERNAL */;
          }else{
            return B(_1o7/* FormEngine.FormElement.FormElement.maybeStr2maybeInt1 */(_1oq/* scii */.a));
          }
        }
      });
      return new T1(1,new T4(4,_1oe/* sch2 */,_1oo/* scik */,new T(function(){
        return B(_1nA/* FormEngine.FormData.getMaybeNumberFIUnitValue */(_1oe/* sch2 */, _1oc/* sch0 */));
      }),_1ob/* scgZ */));
    case 4:
      return new T1(1,new T2(5,_1oe/* sch2 */,_1ob/* scgZ */));
    case 5:
      var _1or/* scis */ = new T(function(){
        return new T3(6,_1oe/* sch2 */,_1os/* scit */,_1ob/* scgZ */);
      }),
      _1os/* scit */ = new T(function(){
        var _1ot/* sciE */ = function(_1ou/* sciu */){
          var _1ov/* sciv */ = E(_1ou/* sciu */);
          if(!_1ov/* sciv */._){
            return new T2(0,_1ov/* sciv */,new T(function(){
              return B(_1nO/* FormEngine.FormData.isOptionSelected */(_1ov/* sciv */, _1oe/* sch2 */, _1oc/* sch0 */));
            }));
          }else{
            var _1ow/* sciD */ = new T(function(){
              return B(_1nW/* Data.Maybe.mapMaybe */(function(_1ox/* B1 */){
                return new F(function(){return _1oa/* FormEngine.FormElement.FormElement.makeElem */(_1or/* scis */, _1oc/* sch0 */, _1ox/* B1 */);});
              }, _1ov/* sciv */.c));
            });
            return new T3(1,_1ov/* sciv */,new T(function(){
              return B(_1nO/* FormEngine.FormData.isOptionSelected */(_1ov/* sciv */, _1oe/* sch2 */, _1oc/* sch0 */));
            }),_1ow/* sciD */);
          }
        };
        return B(_8H/* GHC.Base.map */(_1ot/* sciE */, _1oe/* sch2 */.b));
      });
      return new T1(1,_1or/* scis */);
    case 6:
      var _1oy/* sciW */ = new T(function(){
        var _1oz/* sciH */ = E(_1oc/* sch0 */);
        if(!_1oz/* sciH */._){
          return __Z/* EXTERNAL */;
        }else{
          return B(_1nu/* GHC.List.lookup */(_aM/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_27/* FormEngine.FormItem.numbering2text */(E(_1oe/* sch2 */.a).b));
          }), _1oz/* sciH */.a));
        }
      });
      return new T1(1,new T3(7,_1oe/* sch2 */,_1oy/* sciW */,_1ob/* scgZ */));
    case 7:
      return __Z/* EXTERNAL */;
    case 8:
      var _1oA/* scj3 */ = new T(function(){
        return new T3(8,_1oe/* sch2 */,_1oB/* scj4 */,_1ob/* scgZ */);
      }),
      _1oB/* scj4 */ = new T(function(){
        return B(_1nW/* Data.Maybe.mapMaybe */(function(_1ox/* B1 */){
          return new F(function(){return _1oa/* FormEngine.FormElement.FormElement.makeElem */(_1oA/* scj3 */, _1oc/* sch0 */, _1ox/* B1 */);});
        }, _1oe/* sch2 */.c));
      });
      return new T1(1,_1oA/* scj3 */);
    case 9:
      var _1oC/* scja */ = new T(function(){
        return new T4(9,_1oe/* sch2 */,new T(function(){
          return B(_1nJ/* FormEngine.FormData.isCheckboxChecked */(_1oe/* sch2 */, _1oc/* sch0 */));
        }),_1oD/* scjb */,_1ob/* scgZ */);
      }),
      _1oD/* scjb */ = new T(function(){
        return B(_1nW/* Data.Maybe.mapMaybe */(function(_1ox/* B1 */){
          return new F(function(){return _1oa/* FormEngine.FormElement.FormElement.makeElem */(_1oC/* scja */, _1oc/* sch0 */, _1ox/* B1 */);});
        }, _1oe/* sch2 */.c));
      });
      return new T1(1,_1oC/* scja */);
    case 10:
      var _1oE/* scjg */ = new T(function(){
        return new T3(10,_1oe/* sch2 */,_1oF/* scjh */,_1ob/* scgZ */);
      }),
      _1oF/* scjh */ = new T(function(){
        return B(_1nW/* Data.Maybe.mapMaybe */(function(_1ox/* B1 */){
          return new F(function(){return _1oa/* FormEngine.FormElement.FormElement.makeElem */(_1oE/* scjg */, _1oc/* sch0 */, _1ox/* B1 */);});
        }, _1oe/* sch2 */.c));
      });
      return new T1(1,_1oE/* scjg */);
    case 11:
      return new T1(1,new T2(11,_1oe/* sch2 */,_1ob/* scgZ */));
    default:
      return new T1(1,new T2(12,_1oe/* sch2 */,_1ob/* scgZ */));
  }
},
_1oG/* main4 */ = function(_1oH/* sch2 */){
  var _1oI/* sch3 */ = E(_1oH/* sch2 */);
  if(_1oI/* sch3 */._==7){
    var _1oJ/* sch6 */ = new T(function(){
      return new T3(0,_1oI/* sch3 */,_1oK/* sch7 */,_4x/* GHC.Types.False */);
    }),
    _1oK/* sch7 */ = new T(function(){
      return B(_1nW/* Data.Maybe.mapMaybe */(function(_1oL/* B1 */){
        return new F(function(){return _1oa/* FormEngine.FormElement.FormElement.makeElem */(_1oJ/* sch6 */, _4y/* GHC.Base.Nothing */, _1oL/* B1 */);});
      }, _1oI/* sch3 */.b));
    });
    return new T1(1,_1oJ/* sch6 */);
  }else{
    return __Z/* EXTERNAL */;
  }
},
_1oM/* main_tabMaybes */ = new T(function(){
  return B(_8H/* GHC.Base.map */(_1oG/* Main.main4 */, _1nt/* Questionnaire.formItems */));
}),
_1oN/* main3 */ = new T(function(){
  return B(_pe/* Data.Maybe.catMaybes1 */(_1oM/* Main.main_tabMaybes */));
}),
_1oO/* main_go */ = function(_1oP/* sch9 */){
  while(1){
    var _1oQ/* scha */ = E(_1oP/* sch9 */);
    if(!_1oQ/* scha */._){
      return false;
    }else{
      if(!E(_1oQ/* scha */.a)._){
        return true;
      }else{
        _1oP/* sch9 */ = _1oQ/* scha */.b;
        continue;
      }
    }
  }
},
_1oR/* ready_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (f) { jQuery(document).ready(f); })");
}),
_1oS/* main1 */ = function(_/* EXTERNAL */){
  var _1oT/* schy */ = __createJSFunc/* EXTERNAL */(0, function(_/* EXTERNAL */){
    var _1oU/* schh */ = B(_Lz/* FormEngine.JQuery.selectById1 */(_Lx/* Overlay.overlayId */, _/* EXTERNAL */)),
    _1oV/* schk */ = B(_1r/* FormEngine.JQuery.onClick1 */(_Ny/* Overlay.initOverlay2 */, _1oU/* schh */, _/* EXTERNAL */));
    if(!B(_1oO/* Main.main_go */(_1oM/* Main.main_tabMaybes */))){
      var _1oW/* scho */ = B(_MV/* Form.generateForm1 */(_1oN/* Main.main3 */, _/* EXTERNAL */));
      return _1p/* Haste.Prim.Any.jsNull */;
    }else{
      var _1oX/* schr */ = B(_3/* FormEngine.JQuery.errorIO1 */(_NC/* Main.main2 */, _/* EXTERNAL */));
      return _1p/* Haste.Prim.Any.jsNull */;
    }
  }),
  _1oY/* schE */ = __app1/* EXTERNAL */(E(_1oR/* FormEngine.JQuery.ready_f1 */), _1oT/* schy */);
  return new F(function(){return _1/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_1oZ/* main */ = function(_/* EXTERNAL */){
  return new F(function(){return _1oS/* Main.main1 */(_/* EXTERNAL */);});
};

var hasteMain = function() {B(A(_1oZ, [0]));};window.onload = hasteMain;