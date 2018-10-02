//# 1 "mlString.js"
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010-2014 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

// An OCaml string is an object with three fields:
// - tag 't'
// - length 'l'
// - contents 'c'
//
// The contents of the string can be either a JavaScript array or
// a JavaScript string. The length of this string can be less than the
// length of the OCaml string. In this case, remaining bytes are
// assumed to be zeroes. Arrays are mutable but consumes more memory
// than strings. A common pattern is to start from an empty string and
// progressively fill it from the start. Partial strings makes it
// possible to implement this efficiently.
//
// When converting to and from UTF-16, we keep track of whether the
// string is composed only of ASCII characters (in which case, no
// conversion needs to be performed) or not.
//
// The string tag can thus take the following values:
//   full string     BYTE | UNKNOWN:      0
//                   BYTE | ASCII:        9
//                   BYTE | NOT_ASCII:    8
//   string prefix   PARTIAL:             2
//   array           ARRAY:               4
//
// One can use bit masking to discriminate these different cases:
//   known_encoding(x) = x&8
//   is_ascii(x) =       x&1
//   kind(x) =           x&6

//Provides: caml_str_repeat
function caml_str_repeat(n, s) {
  if (s.repeat) return s.repeat(n); // ECMAscript 6 and Firefox 24+
  var r = "", l = 0;
  if (n == 0) return r;
  for(;;) {
    if (n & 1) r += s;
    n >>= 1;
    if (n == 0) return r;
    s += s;
    l++;
    if (l == 9) {
      s.slice(0,1); // flatten the string
      // then, the flattening of the whole string will be faster,
      // as it will be composed of larger pieces
    }
  }
}

//Provides: caml_subarray_to_string
//Requires: raw_array_sub
function caml_subarray_to_string (a, i, len) {
  var f = String.fromCharCode;
  if (i == 0 && len <= 4096 && len == a.length) return f.apply (null, a);
  var s = "";
  for (; 0 < len; i += 1024,len-=1024)
    s += f.apply (null, raw_array_sub(a,i, Math.min(len, 1024)));
  return s;
}

//Provides: caml_utf8_of_utf16
function caml_utf8_of_utf16(s) {
  for (var b = "", t = b, c, d, i = 0, l = s.length; i < l; i++) {
    c = s.charCodeAt(i);
    if (c < 0x80) {
      for (var j = i + 1; (j < l) && (c = s.charCodeAt(j)) < 0x80; j++);
      if (j - i > 512) { t.substr(0, 1); b += t; t = ""; b += s.slice(i, j) }
      else t += s.slice(i, j);
      if (j == l) break;
      i = j;
    }
    if (c < 0x800) {
      t += String.fromCharCode(0xc0 | (c >> 6));
      t += String.fromCharCode(0x80 | (c & 0x3f));
    } else if (c < 0xd800 || c >= 0xdfff) {
      t += String.fromCharCode(0xe0 | (c >> 12),
                               0x80 | ((c >> 6) & 0x3f),
                               0x80 | (c & 0x3f));
    } else if (c >= 0xdbff || i + 1 == l ||
               (d = s.charCodeAt(i + 1)) < 0xdc00 || d > 0xdfff) {
      // Unmatched surrogate pair, replaced by \ufffd (replacement character)
      t += "\xef\xbf\xbd";
    } else {
      i++;
      c = (c << 10) + d - 0x35fdc00;
      t += String.fromCharCode(0xf0 | (c >> 18),
                               0x80 | ((c >> 12) & 0x3f),
                               0x80 | ((c >> 6) & 0x3f),
                               0x80 | (c & 0x3f));
    }
    if (t.length > 1024) {t.substr(0, 1); b += t; t = "";}
  }
  return b+t;
}

//Provides: caml_utf16_of_utf8
function caml_utf16_of_utf8(s) {
  for (var b = "", t = "", c, c1, c2, v, i = 0, l = s.length; i < l; i++) {
    c1 = s.charCodeAt(i);
    if (c1 < 0x80) {
      for (var j = i + 1; (j < l) && (c1 = s.charCodeAt(j)) < 0x80; j++);
      if (j - i > 512) { t.substr(0, 1); b += t; t = ""; b += s.slice(i, j) }
      else t += s.slice(i, j);
      if (j == l) break;
      i = j;
    }
    v = 1;
    if ((++i < l) && (((c2 = s.charCodeAt(i)) & -64) == 128)) {
      c = c2 + (c1 << 6);
      if (c1 < 0xe0) {
        v = c - 0x3080;
        if (v < 0x80) v = 1;
      } else {
        v = 2;
        if ((++i < l) && (((c2 = s.charCodeAt(i)) & -64) == 128)) {
          c = c2 + (c << 6);
          if (c1 < 0xf0) {
            v = c - 0xe2080;
            if ((v < 0x800) || ((v >= 0xd7ff) && (v < 0xe000))) v = 2;
          } else {
              v = 3;
              if ((++i < l) && (((c2 = s.charCodeAt(i)) & -64) == 128) &&
                  (c1 < 0xf5)) {
                v = c2 - 0x3c82080 + (c << 6);
                if (v < 0x10000 || v > 0x10ffff) v = 3;
              }
          }
        }
      }
    }
    if (v < 4) { // Invalid sequence
      i -= v;
      t += "\ufffd";
    } else if (v > 0xffff)
      t += String.fromCharCode(0xd7c0 + (v >> 10), 0xdc00 + (v & 0x3FF))
    else
      t += String.fromCharCode(v);
    if (t.length > 1024) {t.substr(0, 1); b += t; t = "";}
  }
  return b+t;
}

//Provides: caml_is_ascii
function caml_is_ascii (s) {
  // The regular expression gets better at around this point for all browsers
  if (s.length < 24) {
    // Spidermonkey gets much slower when s.length >= 24 (on 64 bit archs)
    for (var i = 0; i < s.length; i++) if (s.charCodeAt(i) > 127) return false;
    return true;
  } else
    return !/[^\x00-\x7f]/.test(s);
}

//Provides: caml_to_js_string
//Requires: caml_convert_string_to_bytes, caml_is_ascii, caml_utf16_of_utf8
function caml_to_js_string(s) {
  switch (s.t) {
  case 9: /*BYTES | ASCII*/
    return s.c;
  default:
    caml_convert_string_to_bytes(s);
  case 0: /*BYTES | UNKOWN*/
    if (caml_is_ascii(s.c)) {
      s.t = 9; /*BYTES | ASCII*/
      return s.c;
    }
    s.t = 8; /*BYTES | NOT_ASCII*/
  case 8: /*BYTES | NOT_ASCII*/
    return caml_utf16_of_utf8(s.c);
  }
}

//Provides: caml_string_unsafe_get mutable
function caml_string_unsafe_get (s, i) {
  switch (s.t & 6) {
  default: /* PARTIAL */
    if (i >= s.c.length) return 0;
  case 0: /* BYTES */
    return s.c.charCodeAt(i);
  case 4: /* ARRAY */
    return s.c[i]
  }
}

//Provides: caml_bytes_unsafe_get mutable
function caml_bytes_unsafe_get (s, i) {
  switch (s.t & 6) {
  default: /* PARTIAL */
    if (i >= s.c.length) return 0;
  case 0: /* BYTES */
    return s.c.charCodeAt(i);
  case 4: /* ARRAY */
    return s.c[i]
  }
}

//Provides: caml_bytes_unsafe_set
//Requires: caml_convert_string_to_array
function caml_bytes_unsafe_set (s, i, c) {
  // The OCaml compiler uses Char.unsafe_chr on integers larger than 255!
  c &= 0xff;
  if (s.t != 4 /* ARRAY */) {
    if (i == s.c.length) {
      s.c += String.fromCharCode (c);
      if (i + 1 == s.l) s.t = 0; /*BYTES | UNKOWN*/
      return 0;
    }
    caml_convert_string_to_array (s);
  }
  s.c[i] = c;
  return 0;
}

//Provides: caml_string_unsafe_set
//Requires: caml_bytes_unsafe_set
function caml_string_unsafe_set (s, i, c) {
    return caml_bytes_unsafe_set(s,i,c);
}

//Provides: caml_string_bound_error
//Requires: caml_invalid_argument
function caml_string_bound_error () {
  caml_invalid_argument ("index out of bounds");
}

//Provides: caml_string_get
//Requires: caml_string_bound_error, caml_string_unsafe_get
function caml_string_get (s, i) {
  if (i >>> 0 >= s.l) caml_string_bound_error();
  return caml_string_unsafe_get (s, i);
}

//Provides: caml_string_get16
//Requires: caml_string_unsafe_get, caml_string_bound_error
function caml_string_get16(s,i) {
  if (i >>> 0 >= s.l + 1) caml_string_bound_error();
  var b1 = caml_string_unsafe_get (s, i),
      b2 = caml_string_unsafe_get (s, i + 1);
  return (b2 << 8 | b1);
}

//Provides: caml_bytes_get16
//Requires: caml_string_unsafe_get, caml_string_bound_error
function caml_bytes_get16(s,i) {
  if (i >>> 0 >= s.l + 1) caml_string_bound_error();
  var b1 = caml_string_unsafe_get (s, i),
      b2 = caml_string_unsafe_get (s, i + 1);
  return (b2 << 8 | b1);
}

//Provides: caml_string_get32
//Requires: caml_string_unsafe_get, caml_string_bound_error
function caml_string_get32(s,i) {
  if (i >>> 0 >= s.l + 3) caml_string_bound_error();
  var b1 = caml_string_unsafe_get (s, i),
      b2 = caml_string_unsafe_get (s, i + 1),
      b3 = caml_string_unsafe_get (s, i + 2),
      b4 = caml_string_unsafe_get (s, i + 3);
  return (b4 << 24 | b3 << 16 | b2 << 8 | b1);
}

//Provides: caml_bytes_get32
//Requires: caml_string_unsafe_get, caml_string_bound_error
function caml_bytes_get32(s,i) {
  if (i >>> 0 >= s.l + 3) caml_string_bound_error();
  var b1 = caml_string_unsafe_get (s, i),
      b2 = caml_string_unsafe_get (s, i + 1),
      b3 = caml_string_unsafe_get (s, i + 2),
      b4 = caml_string_unsafe_get (s, i + 3);
  return (b4 << 24 | b3 << 16 | b2 << 8 | b1);
}

//Provides: caml_string_get64
//Requires: caml_string_unsafe_get, caml_string_bound_error
//Requires: caml_int64_of_bytes
function caml_string_get64(s,i) {
  if (i >>> 0 >= s.l + 7) caml_string_bound_error();
  var a = new Array(8);
  for(var j = 0; j < 8; j++){
    a[7 - j] = caml_string_unsafe_get (s, i + j);
  }
  return caml_int64_of_bytes(a);
}

//Provides: caml_bytes_get64
//Requires: caml_string_unsafe_get, caml_string_bound_error
//Requires: caml_int64_of_bytes
function caml_bytes_get64(s,i) {
  if (i >>> 0 >= s.l + 7) caml_string_bound_error();
  var a = new Array(8);
  for(var j = 0; j < 8; j++){
    a[7 - j] = caml_string_unsafe_get (s, i + j);
  }
  return caml_int64_of_bytes(a);
}

//Provides: caml_bytes_get
//Requires: caml_string_bound_error, caml_bytes_unsafe_get
function caml_bytes_get (s, i) {
  if (i >>> 0 >= s.l) caml_string_bound_error();
  return caml_bytes_unsafe_get (s, i);
}

//Provides: caml_string_set
//Requires: caml_string_unsafe_set, caml_string_bound_error
function caml_string_set (s, i, c) {
  if (i >>> 0 >= s.l) caml_string_bound_error();
  return caml_string_unsafe_set (s, i, c);
}

//Provides: caml_bytes_set16
//Requires: caml_string_bound_error, caml_string_unsafe_set
function caml_bytes_set16(s,i,i16){
  if (i >>> 0 >= s.l + 1) caml_string_bound_error();
  var b2 = 0xFF & i16 >> 8,
      b1 = 0xFF & i16;
  caml_string_unsafe_set (s, i + 0, b1);
  caml_string_unsafe_set (s, i + 1, b2);
  return 0
}

//Provides: caml_string_set16
//Requires: caml_bytes_set16
function caml_string_set16(s,i,i16){
    return caml_bytes_set16(s,i,i16);
}

//Provides: caml_bytes_set32
//Requires: caml_string_bound_error, caml_string_unsafe_set
function caml_bytes_set32(s,i,i32){
  if (i >>> 0 >= s.l + 3) caml_string_bound_error();
  var b4 = 0xFF & i32 >> 24,
      b3 = 0xFF & i32 >> 16,
      b2 = 0xFF & i32 >> 8,
      b1 = 0xFF & i32;
  caml_string_unsafe_set (s, i + 0, b1);
  caml_string_unsafe_set (s, i + 1, b2);
  caml_string_unsafe_set (s, i + 2, b3);
  caml_string_unsafe_set (s, i + 3, b4);
  return 0
}

//Provides: caml_string_set32
//Requires: caml_bytes_set32
function caml_string_set32(s,i,i32){
    return caml_bytes_set32(s,i,i32);
}

//Provides: caml_bytes_set64
//Requires: caml_string_bound_error, caml_string_unsafe_set
//Requires: caml_int64_to_bytes
function caml_bytes_set64(s,i,i64){
  if (i >>> 0 >= s.l + 7) caml_string_bound_error();
  var a = caml_int64_to_bytes(i64);
  for(var j = 0; j < 8; j++) {
    caml_string_unsafe_set (s, i + 7 - j, a[j]);
  }
  return 0
}

//Provides: caml_string_set64
//Requires: caml_bytes_set64
function caml_string_set64(s,i,i64){
    return caml_bytes_set64(s,i,i64);
}

//Provides: caml_bytes_set
//Requires: caml_string_bound_error, caml_bytes_unsafe_set
function caml_bytes_set (s, i, c) {
  if (i >>> 0 >= s.l) caml_string_bound_error();
  return caml_bytes_unsafe_set (s, i, c);
}

//Provides: MlBytes
//Requires: caml_to_js_string
function MlBytes (tag, contents, length) {
  this.t=tag; this.c=contents; this.l=length;
}
MlBytes.prototype.toString = function(){return caml_to_js_string(this)};

//Provides: caml_convert_string_to_bytes
//Requires: caml_str_repeat, caml_subarray_to_string
function caml_convert_string_to_bytes (s) {
  /* Assumes not BYTES */
  if (s.t == 2 /* PARTIAL */)
    s.c += caml_str_repeat(s.l - s.c.length, '\0')
  else
    s.c = caml_subarray_to_string (s.c, 0, s.c.length);
  s.t = 0; /*BYTES | UNKOWN*/
}

//Provides: caml_convert_string_to_array
function caml_convert_string_to_array (s) {
  /* Assumes not ARRAY */
  if(joo_global_object.Uint8Array) {
    var a = new joo_global_object.Uint8Array(s.l);
  } else {
    var a = new Array(s.l);
  }
  var b = s.c, l = b.length, i = 0;
  for (; i < l; i++) a[i] = b.charCodeAt(i);
  for (l = s.l; i < l; i++) a[i] = 0;
  s.c = a;
  s.t = 4; /* ARRAY */
  return a;
}

//Provides: caml_array_of_string mutable
//Requires: caml_convert_string_to_array
function caml_array_of_string (s) {
  if (s.t != 4 /* ARRAY */) caml_convert_string_to_array(s);
  return s.c;
}

//Provides: caml_jsbytes_of_string mutable
//Requires: caml_convert_string_to_bytes
function caml_jsbytes_of_string (s) {
  if ((s.t & 6) != 0 /* BYTES */) caml_convert_string_to_bytes(s);
  return s.c;
}

//Provides: caml_js_to_string const
//Requires: caml_is_ascii, caml_utf8_of_utf16, MlBytes
function caml_js_to_string (s) {
  var tag = 9 /* BYTES | ASCII */;
  if (!caml_is_ascii(s))
    tag = 8 /* BYTES | NOT_ASCII */, s = caml_utf8_of_utf16(s);
  return new MlBytes(tag, s, s.length);
}

//Provides: caml_create_string const
//Requires: MlBytes,caml_invalid_argument
function caml_create_string(len) {
  if (len < 0) caml_invalid_argument("String.create");
  return new MlBytes(len?2:9,"",len);
}
//Provides: caml_create_bytes const
//Requires: MlBytes,caml_invalid_argument
function caml_create_bytes(len) {
  if (len < 0) caml_invalid_argument("Bytes.create");
  return new MlBytes(len?2:9,"",len);
}

//Provides: caml_new_string const (const)
//Requires: MlBytes
function caml_new_string (s) { return new MlBytes(0,s,s.length); }

//Provides: caml_string_of_array
//Requires: MlBytes
function caml_string_of_array (a) { return new MlBytes(4,a,a.length); }

//Provides: caml_string_compare mutable
//Requires: caml_convert_string_to_bytes
function caml_string_compare(s1, s2) {
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c < s2.c)?-1:(s1.c > s2.c)?1:0;
}


//Provides: caml_bytes_compare mutable
//Requires: caml_convert_string_to_bytes
function caml_bytes_compare(s1, s2) {
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c < s2.c)?-1:(s1.c > s2.c)?1:0;
}

//Provides: caml_string_equal mutable (const, const)
//Requires: caml_convert_string_to_bytes
function caml_string_equal(s1, s2) {
  if(s1 === s2) return 1;
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c == s2.c)?1:0;
}

//Provides: caml_bytes_equal mutable (const, const)
//Requires: caml_convert_string_to_bytes
function caml_bytes_equal(s1, s2) {
  if(s1 === s2) return 1;
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c == s2.c)?1:0;
}

//Provides: caml_string_notequal mutable (const, const)
//Requires: caml_string_equal
function caml_string_notequal(s1, s2) { return 1-caml_string_equal(s1, s2); }

//Provides: caml_bytes_notequal mutable (const, const)
//Requires: caml_string_equal
function caml_bytes_notequal(s1, s2) { return 1-caml_string_equal(s1, s2); }

//Provides: caml_string_lessequal mutable
//Requires: caml_convert_string_to_bytes
function caml_string_lessequal(s1, s2) {
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c <= s2.c)?1:0;
}

//Provides: caml_bytes_lessequal mutable
//Requires: caml_convert_string_to_bytes
function caml_bytes_lessequal(s1, s2) {
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c <= s2.c)?1:0;
}

//Provides: caml_string_lessthan mutable
//Requires: caml_convert_string_to_bytes
function caml_string_lessthan(s1, s2) {
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c < s2.c)?1:0;
}

//Provides: caml_bytes_lessthan mutable
//Requires: caml_convert_string_to_bytes
function caml_bytes_lessthan(s1, s2) {
  (s1.t & 6) && caml_convert_string_to_bytes(s1);
  (s2.t & 6) && caml_convert_string_to_bytes(s2);
  return (s1.c < s2.c)?1:0;
}

//Provides: caml_string_greaterequal
//Requires: caml_string_lessequal
function caml_string_greaterequal(s1, s2) {
  return caml_string_lessequal(s2,s1);
}
//Provides: caml_bytes_greaterequal
//Requires: caml_bytes_lessequal
function caml_bytes_greaterequal(s1, s2) {
  return caml_bytes_lessequal(s2,s1);
}

//Provides: caml_string_greaterthan
//Requires: caml_string_lessthan
function caml_string_greaterthan(s1, s2) {
  return caml_string_lessthan(s2, s1);
}

//Provides: caml_bytes_greaterthan
//Requires: caml_bytes_lessthan
function caml_bytes_greaterthan(s1, s2) {
  return caml_bytes_lessthan(s2, s1);
}

//Provides: caml_fill_bytes
//Requires: caml_str_repeat, caml_convert_string_to_array
function caml_fill_bytes(s, i, l, c) {
  if (l > 0) {
    if (i == 0 && (l >= s.l || (s.t == 2 /* PARTIAL */ && l >= s.c.length))) {
      if (c == 0) {
        s.c = "";
        s.t = 2; /* PARTIAL */
      } else {
        s.c = caml_str_repeat (l, String.fromCharCode(c));
        s.t = (l == s.l)?0 /* BYTES | UNKOWN */ :2; /* PARTIAL */
      }
    } else {
      if (s.t != 4 /* ARRAY */) caml_convert_string_to_array(s);
      for (l += i; i < l; i++) s.c[i] = c;
    }
  }
  return 0;
}

//Provides: caml_fill_string
//Requires: caml_fill_bytes
var caml_fill_string = caml_fill_bytes

//Provides: caml_blit_bytes
//Requires: caml_subarray_to_string, caml_convert_string_to_array
function caml_blit_bytes(s1, i1, s2, i2, len) {
  if (len == 0) return 0;
  if ((i2 == 0) &&
      (len >= s2.l || (s2.t == 2 /* PARTIAL */ && len >= s2.c.length))) {
    s2.c = (s1.t == 4 /* ARRAY */)?
             caml_subarray_to_string(s1.c, i1, len):
             (i1 == 0 && s1.c.length == len)?s1.c:s1.c.substr(i1, len);
    s2.t = (s2.c.length == s2.l)?0 /* BYTES | UNKOWN */ :2; /* PARTIAL */
  } else if (s2.t == 2 /* PARTIAL */ && i2 == s2.c.length) {
    s2.c += (s1.t == 4 /* ARRAY */)?
             caml_subarray_to_string(s1.c, i1, len):
             (i1 == 0 && s1.c.length == len)?s1.c:s1.c.substr(i1, len);
    s2.t = (s2.c.length == s2.l)?0 /* BYTES | UNKOWN */ :2; /* PARTIAL */
  } else {
    if (s2.t != 4 /* ARRAY */) caml_convert_string_to_array(s2);
    var c1 = s1.c, c2 = s2.c;
    if (s1.t == 4 /* ARRAY */) {
        if (i2 <= i1) {
          for (var i = 0; i < len; i++) c2 [i2 + i] = c1 [i1 + i];
        } else {
          for (var i = len - 1; i >= 0; i--) c2 [i2 + i] = c1 [i1 + i];
        }
   } else {
      var l = Math.min (len, c1.length - i1);
      for (var i = 0; i < l; i++) c2 [i2 + i] = c1.charCodeAt(i1 + i);
      for (; i < len; i++) c2 [i2 + i] = 0;
    }
  }
  return 0;
}

//Provides: caml_blit_string
//Requires: caml_blit_bytes
function caml_blit_string(s1, i1, s2, i2, len) {
  // TODO: s1 -> string to bytes
  return caml_blit_bytes(s1, i1, s2, i2, len);
}

//Provides: caml_ml_string_length const
function caml_ml_string_length(s) { return s.l }

//Provides: caml_ml_bytes_length const
function caml_ml_bytes_length(s) { return s.l }

//Provides: caml_string_of_bytes const
function caml_string_of_bytes(s) { return s}

//Provides: caml_bytes_of_string const
function caml_bytes_of_string(s) { return s}

//# 1 "ieee_754.js"
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

//Provides: jsoo_floor_log2
var log2_ok = Math.log2 && Math.log2(1.1235582092889474E+307) == 1020
function jsoo_floor_log2(x) {
    if(log2_ok) return Math.floor(Math.log2(x))
    var i = 0;
    if (x == 0) return -Infinity;
    if(x>=1) {while (x>=2) {x/=2; i++} }
    else {while (x < 1) {x*=2; i--} };
    return i;
}

//Provides: caml_int64_bits_of_float const
//Requires: jsoo_floor_log2
function caml_int64_bits_of_float (x) {
  if (!isFinite(x)) {
    if (isNaN(x)) return [255, 1, 0, 0x7ff0];
    return (x > 0)?[255,0,0,0x7ff0]:[255,0,0,0xfff0];
  }
  var sign = (x==0 && 1/x == -Infinity)?0x8000:(x>=0)?0:0x8000;
  if (sign) x = -x;
  // Int64.bits_of_float 1.1235582092889474E+307 = 0x7fb0000000000000L
  // using Math.LOG2E*Math.log(x) in place of Math.log2 result in precision lost
  var exp = jsoo_floor_log2(x) + 1023;
  if (exp <= 0) {
    exp = 0;
    x /= Math.pow(2,-1026);
  } else {
    x /= Math.pow(2,exp-1027);
    if (x < 16) {
      x *= 2; exp -=1; }
    if (exp == 0) {
      x /= 2; }
  }
  var k = Math.pow(2,24);
  var r3 = x|0;
  x = (x - r3) * k;
  var r2 = x|0;
  x = (x - r2) * k;
  var r1 = x|0;
  r3 = (r3 &0xf) | sign | exp << 4;
  return [255, r1, r2, r3];
}

//Provides: caml_int32_bits_of_float const
//Requires: jsoo_floor_log2
function caml_int32_bits_of_float (x) {
  var float32a = new joo_global_object.Float32Array(1);
  float32a[0] = x;
  var int32a = new joo_global_object.Int32Array(float32a.buffer);
  return int32a[0] | 0;
}

//FP literals can be written using the hexadecimal
//notation 0x<mantissa in hex>p<exponent> from ISO C99.
//https://github.com/dankogai/js-hexfloat/blob/master/hexfloat.js
//Provides: caml_hexstring_of_float const
//Requires: caml_js_to_string, caml_str_repeat
function caml_hexstring_of_float (x, prec, style) {
  if (!isFinite(x)) {
    if (isNaN(x)) return caml_js_to_string("nan");
    return caml_js_to_string ((x > 0)?"infinity":"-infinity");
  }
  var sign = (x==0 && 1/x == -Infinity)?1:(x>=0)?0:1;
  if(sign) x = -x;
  var exp = 0;
  if (x == 0) { }
  else if (x < 1) {
    while (x < 1 && exp > -1022)  { x *= 2; exp-- }
  } else {
    while (x >= 2) { x /= 2; exp++ }
  }
  var exp_sign = exp < 0 ? '' : '+';
  var sign_str = '';
  if (sign) sign_str = '-'
  else {
    switch(style){
    case 43 /* '+' */: sign_str = '+'; break;
    case 32 /* ' ' */: sign_str = ' '; break;
    default: break;
    }
  }
  if (prec >= 0 && prec < 13) {
    /* If a precision is given, and is small, round mantissa accordingly */
      var cst = Math.pow(2,prec * 4);
      x = Math.round(x * cst) / cst;
  }
  var x_str = x.toString(16);
  if(prec >= 0){
      var idx = x_str.indexOf('.');
    if(idx<0) {
      x_str += '.' + caml_str_repeat(prec, '0');
    }
    else {
      var size = idx+1+prec;
      if(x_str.length < size)
        x_str += caml_str_repeat(size - x_str.length, '0');
      else
        x_str = x_str.substr(0,size);
    }
  }
  return caml_js_to_string (sign_str + '0x' + x_str + 'p' + exp_sign + exp.toString(10));
}

//Provides: caml_int64_float_of_bits const
function caml_int64_float_of_bits (x) {
  var exp = (x[3] & 0x7fff) >> 4;
  if (exp == 2047) {
      if ((x[1]|x[2]|(x[3]&0xf)) == 0)
        return (x[3] & 0x8000)?(-Infinity):Infinity;
      else
        return NaN;
  }
  var k = Math.pow(2,-24);
  var res = (x[1]*k+x[2])*k+(x[3]&0xf);
  if (exp > 0) {
    res += 16;
    res *= Math.pow(2,exp-1027);
  } else
    res *= Math.pow(2,-1026);
  if (x[3] & 0x8000) res = - res;
  return res;
}

//Provides: caml_int32_float_of_bits const
function caml_int32_float_of_bits (x) {
  var int32a = new joo_global_object.Int32Array(1);
  int32a[0] = x;
  var float32a = new joo_global_object.Float32Array(int32a.buffer);
  return float32a[0];
}

//Provides: caml_classify_float const
function caml_classify_float (x) {
  if (isFinite (x)) {
    if (Math.abs(x) >= 2.2250738585072014e-308) return 0;
    if (x != 0) return 1;
    return 2;
  }
  return isNaN(x)?4:3;
}
//Provides: caml_modf_float const
function caml_modf_float (x) {
  if (isFinite (x)) {
    var neg = (1/x) < 0;
    x = Math.abs(x);
    var i = Math.floor (x);
    var f = x - i;
    if (neg) { i = -i; f = -f; }
    return [0, f, i];
  }
  if (isNaN (x)) return [0, NaN, NaN];
  return [0, 1/x, x];
}
//Provides: caml_ldexp_float const
function caml_ldexp_float (x,exp) {
  exp |= 0;
  if (exp > 1023) {
    exp -= 1023;
    x *= Math.pow(2, 1023);
    if (exp > 1023) {  // in case x is subnormal
      exp -= 1023;
      x *= Math.pow(2, 1023);
    }
  }
  if (exp < -1023) {
    exp += 1023;
    x *= Math.pow(2, -1023);
  }
  x *= Math.pow(2, exp);
  return x;
}
//Provides: caml_frexp_float const
//Requires: jsoo_floor_log2
function caml_frexp_float (x) {
  if ((x == 0) || !isFinite(x)) return [0, x, 0];
  var neg = x < 0;
  if (neg) x = - x;
  var exp = jsoo_floor_log2(x) + 1;
  x *= Math.pow(2,-exp);
  if (x < 0.5) { x *= 2; exp -= 1; }
  if (neg) x = - x;
  return [0, x, exp];
}

//Provides: caml_float_compare const
function caml_float_compare (x, y) {
  if (x === y) return 0;
  if (x < y) return -1;
  if (x > y) return 1;
  if (x === x) return 1;
  if (y === y) return -1;
  return 0;
}

//Provides: caml_copysign_float const
function caml_copysign_float (x, y) {
  if (y == 0) y = 1 / y;
  x = Math.abs(x);
  return (y < 0)?(-x):x;
}

//Provides: caml_expm1_float const
function caml_expm1_float (x) {
  var y = Math.exp(x), z = y - 1;
  return (Math.abs(x)>1?z:(z==0?x:x*z/Math.log(y)));
}

//Provides: caml_log1p_float const
function caml_log1p_float (x) {
  var y = 1 + x, z = y - 1;
  return (z==0?x:x*Math.log(y)/z);
}

//Provides: caml_hypot_float const
function caml_hypot_float (x, y) {
  var x = Math.abs(x), y = Math.abs(y);
  var a = Math.max(x, y), b = Math.min(x,y) / (a?a:1);
  return (a * Math.sqrt(1 + b*b));
}

// FIX: these five functions only give approximate results.
//Provides: caml_log10_float const
function caml_log10_float (x) { return Math.LOG10E * Math.log(x); }
//Provides: caml_cosh_float const
function caml_cosh_float (x) { return (Math.exp(x) + Math.exp(-x)) / 2; }
//Provides: caml_sinh_float const
function caml_sinh_float (x) { return (Math.exp(x) - Math.exp(-x)) / 2; }
//Provides: caml_tanh_float const
function caml_tanh_float (x) {
  var y = Math.exp(x), z = Math.exp(-x);
  return (y - z) / (y + z);
}

//# 1 "int64.js"
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

//Provides: caml_int64_offset
var caml_int64_offset = Math.pow(2, -24);

//Provides: caml_int64_ucompare const
function caml_int64_ucompare(x,y) {
  if (x[3] > y[3]) return 1;
  if (x[3] < y[3]) return -1;
  if (x[2] > y[2]) return 1;
  if (x[2] < y[2]) return -1;
  if (x[1] > y[1]) return 1;
  if (x[1] < y[1]) return -1;
  return 0;
}

//Provides: caml_int64_ult const
//Requires: caml_int64_ucompare
function caml_int64_ult(x,y) { return caml_int64_ucompare(x,y) < 0; }

//Provides: caml_int64_compare const
function caml_int64_compare(x,y) {
  var x3 = x[3] << 16;
  var y3 = y[3] << 16;
  if (x3 > y3) return 1;
  if (x3 < y3) return -1;
  if (x[2] > y[2]) return 1;
  if (x[2] < y[2]) return -1;
  if (x[1] > y[1]) return 1;
  if (x[1] < y[1]) return -1;
  return 0;
}

//Provides: caml_int64_neg const
function caml_int64_neg (x) {
  var y1 = - x[1];
  var y2 = - x[2] + (y1 >> 24);
  var y3 = - x[3] + (y2 >> 24);
  return [255, y1 & 0xffffff, y2 & 0xffffff, y3 & 0xffff];
}

//Provides: caml_int64_add const
function caml_int64_add (x, y) {
  var z1 = x[1] + y[1];
  var z2 = x[2] + y[2] + (z1 >> 24);
  var z3 = x[3] + y[3] + (z2 >> 24);
  return [255, z1 & 0xffffff, z2 & 0xffffff, z3 & 0xffff];
}

//Provides: caml_int64_sub const
function caml_int64_sub (x, y) {
  var z1 = x[1] - y[1];
  var z2 = x[2] - y[2] + (z1 >> 24);
  var z3 = x[3] - y[3] + (z2 >> 24);
  return [255, z1 & 0xffffff, z2 & 0xffffff, z3 & 0xffff];
}

//Provides: caml_int64_mul const
//Requires: caml_int64_offset
function caml_int64_mul(x,y) {
  var z1 = x[1] * y[1];
  var z2 = ((z1 * caml_int64_offset) | 0) + x[2] * y[1] + x[1] * y[2];
  var z3 = ((z2 * caml_int64_offset) | 0) + x[3] * y[1] + x[2] * y[2] + x[1] * y[3];
  return [255, z1 & 0xffffff, z2 & 0xffffff, z3 & 0xffff];
}

//Provides: caml_int64_is_zero const
function caml_int64_is_zero(x) {
  return (x[3]|x[2]|x[1]) == 0;
}

//Provides: caml_int64_is_negative const
function caml_int64_is_negative(x) {
  return (x[3] << 16) < 0;
}

//Provides: caml_int64_is_min_int const
function caml_int64_is_min_int(x) {
  return x[3] == 0x8000 && (x[1]|x[2]) == 0;
}

//Provides: caml_int64_is_minus_one const
function caml_int64_is_minus_one(x) {
  return x[3] == 0xffff && (x[1]&x[2]) == 0xffffff;
}

//Provides: caml_int64_and const
function caml_int64_and (x, y) {
  return [255, x[1]&y[1], x[2]&y[2], x[3]&y[3]];
}

//Provides: caml_int64_or const
function caml_int64_or (x, y) {
  return [255, x[1]|y[1], x[2]|y[2], x[3]|y[3]];
}

//Provides: caml_int64_xor const
function caml_int64_xor (x, y) {
  return [255, x[1]^y[1], x[2]^y[2], x[3]^y[3]];
}

//Provides: caml_int64_shift_left const
function caml_int64_shift_left (x, s) {
  s = s & 63;
  if (s == 0) return x;
  if (s < 24)
    return [255,
            (x[1] << s) & 0xffffff,
            ((x[2] << s) | (x[1] >> (24 - s))) & 0xffffff,
            ((x[3] << s) | (x[2] >> (24 - s))) & 0xffff];
  if (s < 48)
    return [255, 0,
            (x[1] << (s - 24)) & 0xffffff,
            ((x[2] << (s - 24)) | (x[1] >> (48 - s))) & 0xffff];
  return [255, 0, 0, (x[1] << (s - 48)) & 0xffff];
}

//Provides: caml_int64_shift_right_unsigned const
function caml_int64_shift_right_unsigned (x, s) {
  s = s & 63;
  if (s == 0) return x;
  if (s < 24)
    return [255,
            ((x[1] >> s) | (x[2] << (24 - s))) & 0xffffff,
            ((x[2] >> s) | (x[3] << (24 - s))) & 0xffffff,
            (x[3] >> s)];
  if (s < 48)
    return [255,
            ((x[2] >> (s - 24)) | (x[3] << (48 - s))) & 0xffffff,
            (x[3] >> (s - 24)),
            0];
  return [255, (x[3] >> (s - 48)), 0, 0];
}

//Provides: caml_int64_shift_right const
function caml_int64_shift_right (x, s) {
  s = s & 63;
  if (s == 0) return x;
  var h = (x[3] << 16) >> 16;
  if (s < 24)
    return [255,
            ((x[1] >> s) | (x[2] << (24 - s))) & 0xffffff,
            ((x[2] >> s) | (h << (24 - s))) & 0xffffff,
            ((x[3] << 16) >> s) >>> 16];
  var sign = (x[3] << 16) >> 31;
  if (s < 48)
    return [255,
            ((x[2] >> (s - 24)) | (x[3] << (48 - s))) & 0xffffff,
            ((x[3] << 16) >> (s - 24) >> 16) & 0xffffff,
            sign & 0xffff];
  return [255,
          ((x[3] << 16) >> (s - 32)) & 0xffffff,
          sign & 0xffffff, sign & 0xffff];
}

//Provides: caml_int64_lsl1 const
function caml_int64_lsl1 (x) {
  x[3] = (x[3] << 1) | (x[2] >> 23);
  x[2] = ((x[2] << 1) | (x[1] >> 23)) & 0xffffff;
  x[1] = (x[1] << 1) & 0xffffff;
}

//Provides: caml_int64_lsr1 const
function caml_int64_lsr1 (x) {
  x[1] = ((x[1] >>> 1) | (x[2] << 23)) & 0xffffff;
  x[2] = ((x[2] >>> 1) | (x[3] << 23)) & 0xffffff;
  x[3] = x[3] >>> 1;
}

//Provides: caml_int64_udivmod const
//Requires: caml_int64_ucompare, caml_int64_lsl1, caml_int64_lsr1
//Requires: caml_int64_sub
//Requires: caml_obj_dup
function caml_int64_udivmod (x, y) {
  var offset = 0;
  var modulus = caml_obj_dup(x);
  var divisor = caml_obj_dup(y);
  var quotient = [255, 0, 0, 0];
  while (caml_int64_ucompare (modulus, divisor) > 0) {
    offset++;
    caml_int64_lsl1 (divisor);
  }
  while (offset >= 0) {
    offset --;
    caml_int64_lsl1 (quotient);
    if (caml_int64_ucompare (modulus, divisor) >= 0) {
      quotient[1] ++;
      modulus = caml_int64_sub (modulus, divisor);
    }
    caml_int64_lsr1 (divisor);
  }
  return [0,quotient, modulus];
}

//Provides: caml_int64_div const
//Requires: caml_int64_is_zero, caml_raise_zero_divide
//Requires: caml_int64_neg, caml_int64_udivmod
function caml_int64_div (x, y)
{
  if (caml_int64_is_zero (y)) caml_raise_zero_divide ();
  var sign = x[3] ^ y[3];
  if (x[3] & 0x8000) x = caml_int64_neg(x);
  if (y[3] & 0x8000) y = caml_int64_neg(y);
  var q = caml_int64_udivmod(x, y)[1];
  if (sign & 0x8000) q = caml_int64_neg(q);
  return q;
}

//Provides: caml_int64_mod const
//Requires: caml_int64_is_zero, caml_raise_zero_divide
//Requires: caml_int64_neg, caml_int64_udivmod
function caml_int64_mod (x, y)
{
  if (caml_int64_is_zero (y)) caml_raise_zero_divide ();
  var sign = x[3];
  if (x[3] & 0x8000) x = caml_int64_neg(x);
  if (y[3] & 0x8000) y = caml_int64_neg(y);
  var r = caml_int64_udivmod(x, y)[2];
  if (sign & 0x8000) r = caml_int64_neg(r);
  return r;
}

//Provides: caml_int64_of_int32 const
function caml_int64_of_int32 (x) {
  return [255, x & 0xffffff, (x >> 24) & 0xffffff, (x >> 31) & 0xffff]
}

//Provides: caml_int64_to_int32 const
function caml_int64_to_int32 (x) {
  return x[1] | (x[2] << 24);
}

//Provides: caml_int64_to_float const
function caml_int64_to_float (x) {
  return ((x[3] << 16) * Math.pow(2, 32) + x[2] * Math.pow(2, 24)) + x[1];
}

//Provides: caml_int64_of_float const
//Requires: caml_int64_offset
function caml_int64_of_float (x) {
  if (x < 0) x = Math.ceil(x);
  return [255,
          x & 0xffffff,
          Math.floor(x * caml_int64_offset) & 0xffffff,
          Math.floor(x * caml_int64_offset * caml_int64_offset) & 0xffff];
}

//Provides: caml_int64_format const
//Requires: caml_parse_format, caml_finish_formatting
//Requires: caml_int64_is_negative, caml_int64_neg
//Requires: caml_int64_of_int32, caml_int64_udivmod, caml_int64_to_int32
//Requires: caml_int64_is_zero, caml_str_repeat
function caml_int64_format (fmt, x) {
  var f = caml_parse_format(fmt);
  if (f.signedconv && caml_int64_is_negative(x)) {
    f.sign = -1; x = caml_int64_neg(x);
  }
  var buffer = "";
  var wbase = caml_int64_of_int32(f.base);
  var cvtbl = "0123456789abcdef";
  do {
    var p = caml_int64_udivmod(x, wbase);
    x = p[1];
    buffer = cvtbl.charAt(caml_int64_to_int32(p[2])) + buffer;
  } while (! caml_int64_is_zero(x));
  if (f.prec >= 0) {
    f.filler = ' ';
    var n = f.prec - buffer.length;
    if (n > 0) buffer = caml_str_repeat (n, '0') + buffer;
  }
  return caml_finish_formatting(f, buffer);
}

//Provides: caml_int64_of_string
//Requires: caml_parse_sign_and_base, caml_failwith, caml_parse_digit, MlBytes
//Requires: caml_int64_of_int32, caml_int64_udivmod, caml_int64_ult
//Requires: caml_int64_add, caml_int64_mul, caml_int64_neg
//Requires: caml_ml_string_length,caml_string_unsafe_get
function caml_int64_of_string(s) {
  var r = caml_parse_sign_and_base (s);
  var i = r[0], sign = r[1], base = r[2];
  var base64 = caml_int64_of_int32(base);
  var threshold =
    caml_int64_udivmod([255, 0xffffff, 0xfffffff, 0xffff], base64)[1];
  var c = caml_string_unsafe_get(s, i);
  var d = caml_parse_digit(c);
  if (d < 0 || d >= base) caml_failwith("int_of_string");
  var res = caml_int64_of_int32(d);
  for (;;) {
    i++;
    c = caml_string_unsafe_get(s, i);
    if (c == 95) continue;
    d = caml_parse_digit(c);
    if (d < 0 || d >= base) break;
    /* Detect overflow in multiplication base * res */
    if (caml_int64_ult(threshold, res)) caml_failwith("int_of_string");
    d = caml_int64_of_int32(d);
    res = caml_int64_add(caml_int64_mul(base64, res), d);
    /* Detect overflow in addition (base * res) + d */
    if (caml_int64_ult(res, d)) caml_failwith("int_of_string");
  }
  if (i != caml_ml_string_length(s)) caml_failwith("int_of_string");
  if (r[2] == 10 && caml_int64_ult([255, 0, 0, 0x8000], res))
    caml_failwith("int_of_string");
  if (sign < 0) res = caml_int64_neg(res);
  return res;
}

//Provides: caml_int64_of_bytes
function caml_int64_of_bytes(a) {
  return [255, a[7] | (a[6] << 8) | (a[5] << 16),
          a[4] | (a[3] << 8) | (a[2] << 16), a[1] | (a[0] << 8)];
}
//Provides: caml_int64_to_bytes
function caml_int64_to_bytes(x) {
  return [x[3] >> 8, x[3] & 0xff, x[2] >> 16, (x[2] >> 8) & 0xff, x[2] & 0xff,
          x[1] >> 16, (x[1] >> 8) & 0xff, x[1] & 0xff];
}

//# 1 "md5.js"
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.


//Provides: caml_md5_chan
//Requires: caml_md5_string, caml_string_of_array,caml_ml_channels
//Requires: caml_raise_end_of_file, caml_create_bytes  
function caml_md5_chan(chanid,len){
  var chan = caml_ml_channels[chanid];
  var chan_len = chan.file.length();
  if(len<0) len = chan_len - chan.offset;
  if(chan.offset + len > chan_len) caml_raise_end_of_file();
  var buf = caml_create_bytes(len);
  chan.file.read(chan.offset,buf,0,len);
  return caml_md5_string(buf,0,len);
}

//Provides: caml_md5_string
//Requires: caml_string_of_array, caml_convert_string_to_bytes
var caml_md5_string =
function () {
  function add (x, y) { return (x + y) | 0; }
  function xx(q,a,b,x,s,t) {
    a = add(add(a, q), add(x, t));
    return add((a << s) | (a >>> (32 - s)), b);
  }
  function ff(a,b,c,d,x,s,t) {
    return xx((b & c) | ((~b) & d), a, b, x, s, t);
  }
  function gg(a,b,c,d,x,s,t) {
    return xx((b & d) | (c & (~d)), a, b, x, s, t);
  }
  function hh(a,b,c,d,x,s,t) { return xx(b ^ c ^ d, a, b, x, s, t); }
  function ii(a,b,c,d,x,s,t) { return xx(c ^ (b | (~d)), a, b, x, s, t); }

  function md5(buffer, length) {
    var i = length;
    buffer[i >> 2] |= 0x80 << (8 * (i & 3));
    for (i = (i & ~0x3) + 8;(i & 0x3F) < 60 ;i += 4)
      buffer[(i >> 2) - 1] = 0;
    buffer[(i >> 2) -1] = length << 3;
    buffer[i >> 2] = (length >> 29) & 0x1FFFFFFF;

    var w = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476];

    for(i = 0; i < buffer.length; i += 16) {
      var a = w[0], b = w[1], c = w[2], d = w[3];

      a = ff(a, b, c, d, buffer[i+ 0], 7, 0xD76AA478);
      d = ff(d, a, b, c, buffer[i+ 1], 12, 0xE8C7B756);
      c = ff(c, d, a, b, buffer[i+ 2], 17, 0x242070DB);
      b = ff(b, c, d, a, buffer[i+ 3], 22, 0xC1BDCEEE);
      a = ff(a, b, c, d, buffer[i+ 4], 7, 0xF57C0FAF);
      d = ff(d, a, b, c, buffer[i+ 5], 12, 0x4787C62A);
      c = ff(c, d, a, b, buffer[i+ 6], 17, 0xA8304613);
      b = ff(b, c, d, a, buffer[i+ 7], 22, 0xFD469501);
      a = ff(a, b, c, d, buffer[i+ 8], 7, 0x698098D8);
      d = ff(d, a, b, c, buffer[i+ 9], 12, 0x8B44F7AF);
      c = ff(c, d, a, b, buffer[i+10], 17, 0xFFFF5BB1);
      b = ff(b, c, d, a, buffer[i+11], 22, 0x895CD7BE);
      a = ff(a, b, c, d, buffer[i+12], 7, 0x6B901122);
      d = ff(d, a, b, c, buffer[i+13], 12, 0xFD987193);
      c = ff(c, d, a, b, buffer[i+14], 17, 0xA679438E);
      b = ff(b, c, d, a, buffer[i+15], 22, 0x49B40821);

      a = gg(a, b, c, d, buffer[i+ 1], 5, 0xF61E2562);
      d = gg(d, a, b, c, buffer[i+ 6], 9, 0xC040B340);
      c = gg(c, d, a, b, buffer[i+11], 14, 0x265E5A51);
      b = gg(b, c, d, a, buffer[i+ 0], 20, 0xE9B6C7AA);
      a = gg(a, b, c, d, buffer[i+ 5], 5, 0xD62F105D);
      d = gg(d, a, b, c, buffer[i+10], 9, 0x02441453);
      c = gg(c, d, a, b, buffer[i+15], 14, 0xD8A1E681);
      b = gg(b, c, d, a, buffer[i+ 4], 20, 0xE7D3FBC8);
      a = gg(a, b, c, d, buffer[i+ 9], 5, 0x21E1CDE6);
      d = gg(d, a, b, c, buffer[i+14], 9, 0xC33707D6);
      c = gg(c, d, a, b, buffer[i+ 3], 14, 0xF4D50D87);
      b = gg(b, c, d, a, buffer[i+ 8], 20, 0x455A14ED);
      a = gg(a, b, c, d, buffer[i+13], 5, 0xA9E3E905);
      d = gg(d, a, b, c, buffer[i+ 2], 9, 0xFCEFA3F8);
      c = gg(c, d, a, b, buffer[i+ 7], 14, 0x676F02D9);
      b = gg(b, c, d, a, buffer[i+12], 20, 0x8D2A4C8A);

      a = hh(a, b, c, d, buffer[i+ 5], 4, 0xFFFA3942);
      d = hh(d, a, b, c, buffer[i+ 8], 11, 0x8771F681);
      c = hh(c, d, a, b, buffer[i+11], 16, 0x6D9D6122);
      b = hh(b, c, d, a, buffer[i+14], 23, 0xFDE5380C);
      a = hh(a, b, c, d, buffer[i+ 1], 4, 0xA4BEEA44);
      d = hh(d, a, b, c, buffer[i+ 4], 11, 0x4BDECFA9);
      c = hh(c, d, a, b, buffer[i+ 7], 16, 0xF6BB4B60);
      b = hh(b, c, d, a, buffer[i+10], 23, 0xBEBFBC70);
      a = hh(a, b, c, d, buffer[i+13], 4, 0x289B7EC6);
      d = hh(d, a, b, c, buffer[i+ 0], 11, 0xEAA127FA);
      c = hh(c, d, a, b, buffer[i+ 3], 16, 0xD4EF3085);
      b = hh(b, c, d, a, buffer[i+ 6], 23, 0x04881D05);
      a = hh(a, b, c, d, buffer[i+ 9], 4, 0xD9D4D039);
      d = hh(d, a, b, c, buffer[i+12], 11, 0xE6DB99E5);
      c = hh(c, d, a, b, buffer[i+15], 16, 0x1FA27CF8);
      b = hh(b, c, d, a, buffer[i+ 2], 23, 0xC4AC5665);

      a = ii(a, b, c, d, buffer[i+ 0], 6, 0xF4292244);
      d = ii(d, a, b, c, buffer[i+ 7], 10, 0x432AFF97);
      c = ii(c, d, a, b, buffer[i+14], 15, 0xAB9423A7);
      b = ii(b, c, d, a, buffer[i+ 5], 21, 0xFC93A039);
      a = ii(a, b, c, d, buffer[i+12], 6, 0x655B59C3);
      d = ii(d, a, b, c, buffer[i+ 3], 10, 0x8F0CCC92);
      c = ii(c, d, a, b, buffer[i+10], 15, 0xFFEFF47D);
      b = ii(b, c, d, a, buffer[i+ 1], 21, 0x85845DD1);
      a = ii(a, b, c, d, buffer[i+ 8], 6, 0x6FA87E4F);
      d = ii(d, a, b, c, buffer[i+15], 10, 0xFE2CE6E0);
      c = ii(c, d, a, b, buffer[i+ 6], 15, 0xA3014314);
      b = ii(b, c, d, a, buffer[i+13], 21, 0x4E0811A1);
      a = ii(a, b, c, d, buffer[i+ 4], 6, 0xF7537E82);
      d = ii(d, a, b, c, buffer[i+11], 10, 0xBD3AF235);
      c = ii(c, d, a, b, buffer[i+ 2], 15, 0x2AD7D2BB);
      b = ii(b, c, d, a, buffer[i+ 9], 21, 0xEB86D391);

      w[0] = add(a, w[0]);
      w[1] = add(b, w[1]);
      w[2] = add(c, w[2]);
      w[3] = add(d, w[3]);
    }

    var t = new Array(16);
    for (var i = 0; i < 4; i++)
      for (var j = 0; j < 4; j++)
        t[i * 4 + j] = (w[i] >> (8 * j)) & 0xFF;
    return t;
  }

  return function (s, ofs, len) {
    // FIX: maybe we should perform the computation by chunk of 64 bytes
    // as in http://www.myersdaily.org/joseph/javascript/md5.js
    var buf = [];
    switch (s.t & 6) {
    default:
      caml_convert_string_to_bytes(s);
    case 0: /* BYTES */
      var b = s.c;
      for (var i = 0; i < len; i+=4) {
        var j = i + ofs;
        buf[i>>2] =
          b.charCodeAt(j) | (b.charCodeAt(j+1) << 8) |
          (b.charCodeAt(j+2) << 16) | (b.charCodeAt(j+3) << 24);
      }
      for (; i < len; i++) buf[i>>2] |= b.charCodeAt(i + ofs) << (8 * (i & 3));
      break;
    case 4: /* ARRAY */
      var a = s.c;
      for (var i = 0; i < len; i+=4) {
        var j = i + ofs;
        buf[i>>2] = a[j] | (a[j+1] << 8) | (a[j+2] << 16) | (a[j+3] << 24);
      }
      for (; i < len; i++) buf[i>>2] |= a[i + ofs] << (8 * (i & 3));
    }
    return caml_string_of_array(md5(buf, len));
  }
} ();

//# 1 "marshal.js"
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

//Provides: caml_marshal_constants
var caml_marshal_constants = {
  PREFIX_SMALL_BLOCK:         0x80,
  PREFIX_SMALL_INT:           0x40,
  PREFIX_SMALL_STRING:        0x20,
  CODE_INT8:                  0x00,
  CODE_INT16:                 0x01,
  CODE_INT32:                 0x02,
  CODE_INT64:                 0x03,
  CODE_SHARED8:               0x04,
  CODE_SHARED16:              0x05,
  CODE_SHARED32:              0x06,
  CODE_BLOCK32:               0x08,
  CODE_BLOCK64:               0x13,
  CODE_STRING8:               0x09,
  CODE_STRING32:              0x0A,
  CODE_DOUBLE_BIG:            0x0B,
  CODE_DOUBLE_LITTLE:         0x0C,
  CODE_DOUBLE_ARRAY8_BIG:     0x0D,
  CODE_DOUBLE_ARRAY8_LITTLE:  0x0E,
  CODE_DOUBLE_ARRAY32_BIG:    0x0F,
  CODE_DOUBLE_ARRAY32_LITTLE: 0x07,
  CODE_CODEPOINTER:           0x10,
  CODE_INFIXPOINTER:          0x11,
  CODE_CUSTOM:                0x12
}


//Provides: MlBytesReader
//Requires: caml_new_string, caml_jsbytes_of_string
function MlBytesReader (s, i) { this.s = caml_jsbytes_of_string(s); this.i = i; }
MlBytesReader.prototype = {
  read8u:function () { return this.s.charCodeAt(this.i++); },
  read8s:function () { return this.s.charCodeAt(this.i++) << 24 >> 24; },
  read16u:function () {
    var s = this.s, i = this.i;
    this.i = i + 2;
    return (s.charCodeAt(i) << 8) | s.charCodeAt(i + 1)
  },
  read16s:function () {
    var s = this.s, i = this.i;
    this.i = i + 2;
    return (s.charCodeAt(i) << 24 >> 16) | s.charCodeAt(i + 1);
  },
  read32u:function () {
    var s = this.s, i = this.i;
    this.i = i + 4;
    return ((s.charCodeAt(i) << 24) | (s.charCodeAt(i+1) << 16) |
            (s.charCodeAt(i+2) << 8) | s.charCodeAt(i+3)) >>> 0;
  },
  read32s:function () {
    var s = this.s, i = this.i;
    this.i = i + 4;
    return (s.charCodeAt(i) << 24) | (s.charCodeAt(i+1) << 16) |
      (s.charCodeAt(i+2) << 8) | s.charCodeAt(i+3);
  },
  readstr:function (len) {
    var i = this.i;
    this.i = i + len;
    return caml_new_string(this.s.substring(i, i + len));
  }
}

//Provides: BigStringReader
//Requires: caml_string_of_array, caml_ba_get_1
function BigStringReader (bs, i) { this.s = bs; this.i = i; }
BigStringReader.prototype = {
  read8u:function () { return caml_ba_get_1(this.s,this.i++); },
  read8s:function () { return caml_ba_get_1(this.s,this.i++) << 24 >> 24; },
  read16u:function () {
    var s = this.s, i = this.i;
    this.i = i + 2;
    return (caml_ba_get_1(s,i) << 8) | caml_ba_get_1(s,i + 1)
  },
  read16s:function () {
    var s = this.s, i = this.i;
    this.i = i + 2;
    return (caml_ba_get_1(s,i) << 24 >> 16) | caml_ba_get_1(s,i + 1);
  },
  read32u:function () {
    var s = this.s, i = this.i;
    this.i = i + 4;
    return ((caml_ba_get_1(s,i)   << 24) | (caml_ba_get_1(s,i+1) << 16) |
            (caml_ba_get_1(s,i+2) << 8)  | caml_ba_get_1(s,i+3)         ) >>> 0;
  },
  read32s:function () {
    var s = this.s, i = this.i;
    this.i = i + 4;
    return (caml_ba_get_1(s,i)   << 24) | (caml_ba_get_1(s,i+1) << 16) |
	   (caml_ba_get_1(s,i+2) << 8)  | caml_ba_get_1(s,i+3);
  },
  readstr:function (len) {
    var i = this.i;
    var arr = new Array(len)
    for(var j = 0; j < len; j++){
      arr[j] = caml_ba_get_1(this.s, i+j);
    }
    this.i = i + len;
    return caml_string_of_array(arr);
  }
}



//Provides: caml_float_of_bytes
//Requires: caml_int64_float_of_bits, caml_int64_of_bytes
function caml_float_of_bytes (a) {
  return caml_int64_float_of_bits (caml_int64_of_bytes (a));
}

//Provides: caml_input_value_from_string mutable
//Requires: MlBytesReader, caml_input_value_from_reader
function caml_input_value_from_string(s,ofs) {
  var reader = new MlBytesReader (s, typeof ofs=="number"?ofs:ofs[0]);
  return caml_input_value_from_reader(reader, ofs)
}

//Provides: caml_input_value_from_bytes mutable
//Requires: MlBytesReader, caml_input_value_from_reader
function caml_input_value_from_bytes(s,ofs) {
  var reader = new MlBytesReader (s, typeof ofs=="number"?ofs:ofs[0]);
  return caml_input_value_from_reader(reader, ofs)
}

//Provides: caml_input_value_from_reader mutable
//Requires: caml_failwith
//Requires: caml_float_of_bytes, caml_int64_of_bytes

function caml_input_value_from_reader(reader, ofs) {
  var _magic = reader.read32u ()
  var _block_len = reader.read32u ();
  var num_objects = reader.read32u ();
  var _size_32 = reader.read32u ();
  var _size_64 = reader.read32u ();
  var stack = [];
  var intern_obj_table = (num_objects > 0)?[]:null;
  var obj_counter = 0;
  function intern_rec () {
    var code = reader.read8u ();
    if (code >= 0x40 /*cst.PREFIX_SMALL_INT*/) {
      if (code >= 0x80 /*cst.PREFIX_SMALL_BLOCK*/) {
        var tag = code & 0xF;
        var size = (code >> 4) & 0x7;
        var v = [tag];
        if (size == 0) return v;
        if (intern_obj_table) intern_obj_table[obj_counter++] = v;
        stack.push(v, size);
        return v;
      } else
        return (code & 0x3F);
    } else {
      if (code >= 0x20/*cst.PREFIX_SMALL_STRING */) {
        var len = code & 0x1F;
        var v = reader.readstr (len);
        if (intern_obj_table) intern_obj_table[obj_counter++] = v;
        return v;
      } else {
        switch(code) {
        case 0x00: //cst.CODE_INT8:
          return reader.read8s ();
        case 0x01: //cst.CODE_INT16:
          return reader.read16s ();
        case 0x02: //cst.CODE_INT32:
          return reader.read32s ();
        case 0x03: //cst.CODE_INT64:
          caml_failwith("input_value: integer too large");
          break;
        case 0x04: //cst.CODE_SHARED8:
          var offset = reader.read8u ();
          return intern_obj_table[obj_counter - offset];
        case 0x05: //cst.CODE_SHARED16:
          var offset = reader.read16u ();
          return intern_obj_table[obj_counter - offset];
        case 0x06: //cst.CODE_SHARED32:
          var offset = reader.read32u ();
          return intern_obj_table[obj_counter - offset];
        case 0x08: //cst.CODE_BLOCK32:
          var header = reader.read32u ();
          var tag = header & 0xFF;
          var size = header >> 10;
          var v = [tag];
          if (size == 0) return v;
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          stack.push(v, size);
          return v;
        case 0x13: //cst.CODE_BLOCK64:
          caml_failwith ("input_value: data block too large");
          break;
        case 0x09: //cst.CODE_STRING8:
          var len = reader.read8u();
          var v = reader.readstr (len);
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          return v;
        case 0x0A: //cst.CODE_STRING32:
          var len = reader.read32u();
          var v = reader.readstr (len);
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          return v;
        case 0x0C: //cst.CODE_DOUBLE_LITTLE:
          var t = new Array(8);;
          for (var i = 0;i < 8;i++) t[7 - i] = reader.read8u ();
          var v = caml_float_of_bytes (t);
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          return v;
        case 0x0B: //cst.CODE_DOUBLE_BIG:
          var t = new Array(8);;
          for (var i = 0;i < 8;i++) t[i] = reader.read8u ();
          var v = caml_float_of_bytes (t);
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          return v;
        case 0x0E: //cst.CODE_DOUBLE_ARRAY8_LITTLE:
          var len = reader.read8u();
          var v = new Array(len+1);
          v[0] = 254;
          var t = new Array(8);;
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          for (var i = 1;i <= len;i++) {
            for (var j = 0;j < 8;j++) t[7 - j] = reader.read8u();
            v[i] = caml_float_of_bytes (t);
          }
          return v;
        case 0x0D: //cst.CODE_DOUBLE_ARRAY8_BIG:
          var len = reader.read8u();
          var v = new Array(len+1);
          v[0] = 254;
          var t = new Array(8);;
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          for (var i = 1;i <= len;i++) {
            for (var j = 0;j < 8;j++) t[j] = reader.read8u();
            v [i] = caml_float_of_bytes (t);
          }
          return v;
        case 0x07: //cst.CODE_DOUBLE_ARRAY32_LITTLE:
          var len = reader.read32u();
          var v = new Array(len+1);
          v[0] = 254;
          if (intern_obj_table) intern_obj_table[obj_counter++] = v;
          var t = new Array(8);;
          for (var i = 1;i <= len;i++) {
            for (var j = 0;j < 8;j++) t[7 - j] = reader.read8u();
            v[i] = caml_float_of_bytes (t);
          }
          return v;
        case 0x0F: //cst.CODE_DOUBLE_ARRAY32_BIG:
          var len = reader.read32u();
          var v = new Array(len+1);
          v[0] = 254;
          var t = new Array(8);;
          for (var i = 1;i <= len;i++) {
            for (var j = 0;j < 8;j++) t[j] = reader.read8u();
            v [i] = caml_float_of_bytes (t);
          }
          return v;
        case 0x10: //cst.CODE_CODEPOINTER:
        case 0x11: //cst.CODE_INFIXPOINTER:
          caml_failwith ("input_value: code pointer");
          break;
        case 0x12: //cst.CODE_CUSTOM:
          var c, s = "";
          while ((c = reader.read8u ()) != 0) s += String.fromCharCode (c);
          switch(s) {
          case "_j":
            // Int64
            var t = new Array(8);;
            for (var j = 0;j < 8;j++) t[j] = reader.read8u();
            var v = caml_int64_of_bytes (t);
            if (intern_obj_table) intern_obj_table[obj_counter++] = v;
            return v;
          case "_i":
            // Int32
            var v = reader.read32s ();
            if (intern_obj_table) intern_obj_table[obj_counter++] = v;
            return v;
          case "_n":
            // Nativeint
            switch (reader.read8u ()) {
            case 1:
              var v = reader.read32s ();
              if (intern_obj_table) intern_obj_table[obj_counter++] = v;
              return v;
            case 2:
              caml_failwith("input_value: native integer value too large");
            default:
              caml_failwith("input_value: ill-formed native integer");
            }
          default:
            caml_failwith("input_value: unknown custom block identifier");
          }
        default:
          caml_failwith ("input_value: ill-formed message");
        }
      }
    }
  }
  var res = intern_rec ();
  while (stack.length > 0) {
    var size = stack.pop();
    var v = stack.pop();
    var d = v.length;
    if (d < size) stack.push(v, size);
    v[d] = intern_rec ();
  }
  if (typeof ofs!="number") ofs[0] = reader.i;
  return res;
}

//Provides: caml_marshal_data_size mutable
//Requires: caml_failwith, caml_bytes_unsafe_get
function caml_marshal_data_size (s, ofs) {
  function get32(s,i) {
    return (caml_bytes_unsafe_get(s, i) << 24) |
           (caml_bytes_unsafe_get(s, i + 1) << 16) |
           (caml_bytes_unsafe_get(s, i + 2) << 8) |
            caml_bytes_unsafe_get(s, i + 3);
  }
  if (get32(s, ofs) != (0x8495A6BE|0))
    caml_failwith("Marshal.data_size: bad object");
  return (get32(s, ofs + 4));
}

//Provides: caml_output_val
//Requires: caml_int64_to_bytes, caml_failwith
//Requires: caml_int64_bits_of_float
//Requires: MlBytes, caml_ml_string_length, caml_string_unsafe_get
var caml_output_val = function (){
  function Writer () { this.chunk = []; }
  Writer.prototype = {
    chunk_idx:20, block_len:0, obj_counter:0, size_32:0, size_64:0,
    write:function (size, value) {
      for (var i = size - 8;i >= 0;i -= 8)
        this.chunk[this.chunk_idx++] = (value >> i) & 0xFF;
    },
    write_code:function (size, code, value) {
      this.chunk[this.chunk_idx++] = code;
      for (var i = size - 8;i >= 0;i -= 8)
        this.chunk[this.chunk_idx++] = (value >> i) & 0xFF;
    },
    finalize:function () {
      this.block_len = this.chunk_idx - 20;
      this.chunk_idx = 0;
      this.write (32, 0x8495A6BE);
      this.write (32, this.block_len);
      this.write (32, this.obj_counter);
      this.write (32, this.size_32);
      this.write (32, this.size_64);
      return this.chunk;
    }
  }
  return function (v) {
    var writer = new Writer ();
    var stack = [];
    function extern_rec (v) {
      if (v instanceof Array && v[0] === (v[0]|0)) {
        if (v[0] == 255) {
          // Int64
          writer.write (8, 0x12 /*cst.CODE_CUSTOM*/);
          for (var i = 0; i < 3; i++) writer.write (8, "_j\0".charCodeAt(i));
          var b = caml_int64_to_bytes (v);
          for (var i = 0; i < 8; i++) writer.write (8, b[i]);
          writer.size_32 += 4;
          writer.size_64 += 3;
          return;
        }
        if (v[0] == 251) {
          caml_failwith("output_value: abstract value (Abstract)");
        }
        if (v[0] < 16 && v.length - 1 < 8)
          writer.write (8, 0x80 /*cst.PREFIX_SMALL_BLOCK*/ + v[0] + ((v.length - 1)<<4));
        else
          writer.write_code(32, 0x08 /*cst.CODE_BLOCK32*/, ((v.length-1) << 10) | v[0]);
        writer.size_32 += v.length;
        writer.size_64 += v.length;
        if (v.length > 1) stack.push (v, 1);
      } else if (v instanceof MlBytes) {
        var len = caml_ml_string_length(v);
        if (len < 0x20)
          writer.write (8, 0x20 /*cst.PREFIX_SMALL_STRING*/ + len);
        else if (len < 0x100)
          writer.write_code (8, 0x09/*cst.CODE_STRING8*/, len);
        else
          writer.write_code (32, 0x0A /*cst.CODE_STRING32*/, len);
        for (var i = 0;i < len;i++)
          writer.write (8, caml_string_unsafe_get(v,i));
        writer.size_32 += 1 + (((len + 4) / 4)|0);
        writer.size_64 += 1 + (((len + 8) / 8)|0);
      } else {
        if (v != (v|0)){
          var type_of_v = typeof v;
//
// If a float happens to be an integer it is serialized as an integer
// (Js_of_ocaml cannot tell whether the type of an integer number is
// float or integer.) This can result in unexpected crashes when
// unmarshalling using the standard runtime. It seems better to
// systematically fail on marshalling.
//
//          if(type_of_v != "number")
          caml_failwith("output_value: abstract value ("+type_of_v+")");
//          var t = caml_int64_to_bytes(caml_int64_bits_of_float(v));
//          writer.write (8, 0x0B /*cst.CODE_DOUBLE_BIG*/);
//          for(var i = 0; i<8; i++){writer.write(8,t[i])}
        }
        else if (v >= 0 && v < 0x40) {
          writer.write (8, 0X40 /*cst.PREFIX_SMALL_INT*/ + v);
        } else {
          if (v >= -(1 << 7) && v < (1 << 7))
            writer.write_code(8, 0x00 /*cst.CODE_INT8*/, v);
          else if (v >= -(1 << 15) && v < (1 << 15))
            writer.write_code(16, 0x01 /*cst.CODE_INT16*/, v);
          else
            writer.write_code(32, 0x02 /*cst.CODE_INT32*/, v);
        }
      }
    }
    extern_rec (v);
    while (stack.length > 0) {
      var i = stack.pop ();
      var v = stack.pop ();
      if (i + 1 < v.length) stack.push (v, i + 1);
      extern_rec (v[i]);
    }
    writer.finalize ();
    return writer.chunk;
  }
} ();

//Provides: caml_output_value_to_string mutable
//Requires: caml_output_val, caml_string_of_array
function caml_output_value_to_string (v, _fl) {
  /* ignores flags... */
  return caml_string_of_array (caml_output_val (v));
}

//Provides: caml_output_value_to_bytes mutable
//Requires: caml_output_val, caml_string_of_array
function caml_output_value_to_bytes (v, _fl) {
  /* ignores flags... */
  return caml_string_of_array (caml_output_val (v));
}

//Provides: caml_output_value_to_buffer
//Requires: caml_output_val, caml_failwith, caml_blit_bytes
function caml_output_value_to_buffer (s, ofs, len, v, _fl) {
  /* ignores flags... */
  var t = caml_output_val (v);
  if (t.length > len) caml_failwith ("Marshal.to_buffer: buffer overflow");
  caml_blit_bytes(t, 0, s, ofs, t.length);
  return 0;
}

//# 1 "lexing.js"
/***********************************************************************/
/*                                                                     */
/*                           Objective Caml                            */
/*                                                                     */
/*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 1996 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Lesser General Public License, with     */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/

/* $Id: lexing.c 6045 2004-01-01 16:42:43Z doligez $ */

/* The table-driven automaton for lexers generated by camllex. */

//Provides: caml_lex_array
//Requires: caml_jsbytes_of_string
function caml_lex_array(s) {
  s = caml_jsbytes_of_string(s);
  var l = s.length / 2;
  var a = new Array(l);
  for (var i = 0; i < l; i++)
    a[i] = (s.charCodeAt(2 * i) | (s.charCodeAt(2 * i + 1) << 8)) << 16 >> 16;
  return a;
}

//Provides: caml_lex_engine
//Requires: caml_failwith, caml_lex_array, caml_array_of_string
function caml_lex_engine(tbl, start_state, lexbuf) {
  var lex_buffer = 2;
  var lex_buffer_len = 3;
  var lex_start_pos = 5;
  var lex_curr_pos = 6;
  var lex_last_pos = 7;
  var lex_last_action = 8;
  var lex_eof_reached = 9;
  var lex_base = 1;
  var lex_backtrk = 2;
  var lex_default = 3;
  var lex_trans = 4;
  var lex_check = 5;

  if (!tbl.lex_default) {
    tbl.lex_base =    caml_lex_array (tbl[lex_base]);
    tbl.lex_backtrk = caml_lex_array (tbl[lex_backtrk]);
    tbl.lex_check =   caml_lex_array (tbl[lex_check]);
    tbl.lex_trans =   caml_lex_array (tbl[lex_trans]);
    tbl.lex_default = caml_lex_array (tbl[lex_default]);
  }

  var c, state = start_state;

  var buffer = caml_array_of_string(lexbuf[lex_buffer]);

  if (state >= 0) {
    /* First entry */
    lexbuf[lex_last_pos] = lexbuf[lex_start_pos] = lexbuf[lex_curr_pos];
    lexbuf[lex_last_action] = -1;
  } else {
    /* Reentry after refill */
    state = -state - 1;
  }
  for(;;) {
    /* Lookup base address or action number for current state */
    var base = tbl.lex_base[state];
    if (base < 0) return -base-1;
    /* See if it's a backtrack point */
    var backtrk = tbl.lex_backtrk[state];
    if (backtrk >= 0) {
      lexbuf[lex_last_pos] = lexbuf[lex_curr_pos];
      lexbuf[lex_last_action] = backtrk;
    }
    /* See if we need a refill */
    if (lexbuf[lex_curr_pos] >= lexbuf[lex_buffer_len]){
      if (lexbuf[lex_eof_reached] == 0)
        return -state - 1;
      else
        c = 256;
    }else{
      /* Read next input char */
      c = buffer[lexbuf[lex_curr_pos]];
      lexbuf[lex_curr_pos] ++;
    }
    /* Determine next state */
    if (tbl.lex_check[base + c] == state)
      state = tbl.lex_trans[base + c];
    else
      state = tbl.lex_default[state];
    /* If no transition on this char, return to last backtrack point */
    if (state < 0) {
      lexbuf[lex_curr_pos] = lexbuf[lex_last_pos];
      if (lexbuf[lex_last_action] == -1)
        caml_failwith("lexing: empty token");
      else
        return lexbuf[lex_last_action];
    }else{
      /* Erase the EOF condition only if the EOF pseudo-character was
         consumed by the automaton (i.e. there was no backtrack above)
       */
      if (c == 256) lexbuf[lex_eof_reached] = 0;
    }
  }
}

/***********************************************/
/* New lexer engine, with memory of positions  */
/***********************************************/

//Provides: caml_new_lex_engine
//Requires: caml_failwith, caml_lex_array
//Requires: caml_jsbytes_of_string, caml_array_of_string
function caml_lex_run_mem(s, i, mem, curr_pos) {
  for (;;) {
    var dst = s.charCodeAt(i); i++;
    if (dst == 0xff) return;
    var src = s.charCodeAt(i); i++;
    if (src == 0xff)
      mem [dst + 1] = curr_pos;
    else
      mem [dst + 1] = mem [src + 1];
  }
}

function caml_lex_run_tag(s, i, mem) {
  for (;;) {
    var dst = s.charCodeAt(i); i++;
    if (dst == 0xff) return ;
    var src = s.charCodeAt(i); i++;
    if (src == 0xff)
      mem [dst + 1] = -1;
    else
      mem [dst + 1] = mem [src + 1];
  }
}

function caml_new_lex_engine(tbl, start_state, lexbuf) {
  var lex_buffer = 2;
  var lex_buffer_len = 3;
  var lex_start_pos = 5;
  var lex_curr_pos = 6;
  var lex_last_pos = 7;
  var lex_last_action = 8;
  var lex_eof_reached = 9;
  var lex_mem = 10;
  var lex_base = 1;
  var lex_backtrk = 2;
  var lex_default = 3;
  var lex_trans = 4;
  var lex_check = 5;
  var lex_base_code = 6;
  var lex_backtrk_code = 7;
  var lex_default_code = 8;
  var lex_trans_code = 9;
  var lex_check_code = 10;
  var lex_code = 11;

  if (!tbl.lex_default) {
    tbl.lex_base =    caml_lex_array (tbl[lex_base]);
    tbl.lex_backtrk = caml_lex_array (tbl[lex_backtrk]);
    tbl.lex_check =   caml_lex_array (tbl[lex_check]);
    tbl.lex_trans =   caml_lex_array (tbl[lex_trans]);
    tbl.lex_default = caml_lex_array (tbl[lex_default]);
  }
  if (!tbl.lex_default_code) {
    tbl.lex_base_code =    caml_lex_array (tbl[lex_base_code]);
    tbl.lex_backtrk_code = caml_lex_array (tbl[lex_backtrk_code]);
    tbl.lex_check_code =   caml_lex_array (tbl[lex_check_code]);
    tbl.lex_trans_code =   caml_lex_array (tbl[lex_trans_code]);
    tbl.lex_default_code = caml_lex_array (tbl[lex_default_code]);
  }
  if (tbl.lex_code == null) tbl.lex_code = caml_jsbytes_of_string(tbl[lex_code]);

  var c, state = start_state;

  var buffer = caml_array_of_string(lexbuf[lex_buffer]);

  if (state >= 0) {
    /* First entry */
    lexbuf[lex_last_pos] = lexbuf[lex_start_pos] = lexbuf[lex_curr_pos];
    lexbuf[lex_last_action] = -1;
  } else {
    /* Reentry after refill */
    state = -state - 1;
  }
  for(;;) {
    /* Lookup base address or action number for current state */
    var base = tbl.lex_base[state];
    if (base < 0) {
      var pc_off = tbl.lex_base_code[state];
      caml_lex_run_tag(tbl.lex_code, pc_off, lexbuf[lex_mem]);
      return -base-1;
    }
    /* See if it's a backtrack point */
    var backtrk = tbl.lex_backtrk[state];
    if (backtrk >= 0) {
      var pc_off = tbl.lex_backtrk_code[state];
      caml_lex_run_tag(tbl.lex_code, pc_off, lexbuf[lex_mem]);
      lexbuf[lex_last_pos] = lexbuf[lex_curr_pos];
      lexbuf[lex_last_action] = backtrk;
    }
    /* See if we need a refill */
    if (lexbuf[lex_curr_pos] >= lexbuf[lex_buffer_len]){
      if (lexbuf[lex_eof_reached] == 0)
        return -state - 1;
      else
        c = 256;
    }else{
      /* Read next input char */
      c = buffer[lexbuf[lex_curr_pos]];
      lexbuf[lex_curr_pos] ++;
    }
    /* Determine next state */
    var pstate = state ;
    if (tbl.lex_check[base + c] == state)
      state = tbl.lex_trans[base + c];
    else
      state = tbl.lex_default[state];
    /* If no transition on this char, return to last backtrack point */
    if (state < 0) {
      lexbuf[lex_curr_pos] = lexbuf[lex_last_pos];
      if (lexbuf[lex_last_action] == -1)
        caml_failwith("lexing: empty token");
      else
        return lexbuf[lex_last_action];
    }else{
      /* If some transition, get and perform memory moves */
      var base_code = tbl.lex_base_code[pstate], pc_off;
      if (tbl.lex_check_code[base_code + c] == pstate)
        pc_off = tbl.lex_trans_code[base_code + c];
      else
        pc_off = tbl.lex_default_code[pstate];
      if (pc_off > 0)
        caml_lex_run_mem
          (tbl.lex_code, pc_off, lexbuf[lex_mem], lexbuf[lex_curr_pos]);
      /* Erase the EOF condition only if the EOF pseudo-character was
         consumed by the automaton (i.e. there was no backtrack above)
       */
      if (c == 256) lexbuf[lex_eof_reached] = 0;
    }
  }
}


//# 1 "parsing.js"
/***********************************************************************/
/*                                                                     */
/*                           Objective Caml                            */
/*                                                                     */
/*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 1996 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Lesser General Public License, with     */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/

/* $Id: parsing.c 8983 2008-08-06 09:38:25Z xleroy $ */

/* The PDA automaton for parsers generated by camlyacc */

/* The pushdown automata */

//Provides: caml_parse_engine
//Requires: caml_lex_array
function caml_parse_engine(tables, env, cmd, arg)
{
  var ERRCODE = 256;

  //var START = 0;
  //var TOKEN_READ = 1;
  //var STACKS_GROWN_1 = 2;
  //var STACKS_GROWN_2 = 3;
  //var SEMANTIC_ACTION_COMPUTED = 4;
  //var ERROR_DETECTED = 5;
  var loop = 6;
  var testshift = 7;
  var shift = 8;
  var shift_recover = 9;
  var reduce = 10;

  var READ_TOKEN = 0;
  var RAISE_PARSE_ERROR = 1;
  var GROW_STACKS_1 = 2;
  var GROW_STACKS_2 = 3;
  var COMPUTE_SEMANTIC_ACTION = 4;
  var CALL_ERROR_FUNCTION = 5;

  var env_s_stack = 1;
  var env_v_stack = 2;
  var env_symb_start_stack = 3;
  var env_symb_end_stack = 4;
  var env_stacksize = 5;
  var env_stackbase = 6;
  var env_curr_char = 7;
  var env_lval = 8;
  var env_symb_start = 9;
  var env_symb_end = 10;
  var env_asp = 11;
  var env_rule_len = 12;
  var env_rule_number = 13;
  var env_sp = 14;
  var env_state = 15;
  var env_errflag = 16;

  // var _tbl_actions = 1;
  var tbl_transl_const = 2;
  var tbl_transl_block = 3;
  var tbl_lhs = 4;
  var tbl_len = 5;
  var tbl_defred = 6;
  var tbl_dgoto = 7;
  var tbl_sindex = 8;
  var tbl_rindex = 9;
  var tbl_gindex = 10;
  var tbl_tablesize = 11;
  var tbl_table = 12;
  var tbl_check = 13;
  // var _tbl_error_function = 14;
  // var _tbl_names_const = 15;
  // var _tbl_names_block = 16;

  if (!tables.dgoto) {
    tables.defred = caml_lex_array (tables[tbl_defred]);
    tables.sindex = caml_lex_array (tables[tbl_sindex]);
    tables.check  = caml_lex_array (tables[tbl_check]);
    tables.rindex = caml_lex_array (tables[tbl_rindex]);
    tables.table  = caml_lex_array (tables[tbl_table]);
    tables.len    = caml_lex_array (tables[tbl_len]);
    tables.lhs    = caml_lex_array (tables[tbl_lhs]);
    tables.gindex = caml_lex_array (tables[tbl_gindex]);
    tables.dgoto  = caml_lex_array (tables[tbl_dgoto]);
  }

  var res = 0, n, n1, n2, state1;

  // RESTORE
  var sp = env[env_sp];
  var state = env[env_state];
  var errflag = env[env_errflag];

  exit:for (;;) {
    switch(cmd) {
    case 0://START:
      state = 0;
      errflag = 0;
      // Fall through

    case 6://loop:
      n = tables.defred[state];
      if (n != 0) { cmd = reduce; break; }
      if (env[env_curr_char] >= 0) { cmd = testshift; break; }
      res = READ_TOKEN;
      break exit;
                                  /* The ML code calls the lexer and updates */
                                  /* symb_start and symb_end */
    case 1://TOKEN_READ:
      if (arg instanceof Array) {
        env[env_curr_char] = tables[tbl_transl_block][arg[0] + 1];
        env[env_lval] = arg[1];
      } else {
        env[env_curr_char] = tables[tbl_transl_const][arg + 1];
        env[env_lval] = 0;
      }
      // Fall through

    case 7://testshift:
      n1 = tables.sindex[state];
      n2 = n1 + env[env_curr_char];
      if (n1 != 0 && n2 >= 0 && n2 <= tables[tbl_tablesize] &&
          tables.check[n2] == env[env_curr_char]) {
        cmd = shift; break;
      }
      n1 = tables.rindex[state];
      n2 = n1 + env[env_curr_char];
      if (n1 != 0 && n2 >= 0 && n2 <= tables[tbl_tablesize] &&
          tables.check[n2] == env[env_curr_char]) {
        n = tables.table[n2];
        cmd = reduce; break;
      }
      if (errflag <= 0) {
        res = CALL_ERROR_FUNCTION;
        break exit;
      }
      // Fall through
                                  /* The ML code calls the error function */
    case 5://ERROR_DETECTED:
      if (errflag < 3) {
        errflag = 3;
        for (;;) {
          state1 = env[env_s_stack][sp + 1];
          n1 = tables.sindex[state1];
          n2 = n1 + ERRCODE;
          if (n1 != 0 && n2 >= 0 && n2 <= tables[tbl_tablesize] &&
              tables.check[n2] == ERRCODE) {
            cmd = shift_recover; break;
          } else {
            if (sp <= env[env_stackbase]) return RAISE_PARSE_ERROR;
                                    /* The ML code raises Parse_error */
            sp--;
          }
        }
      } else {
        if (env[env_curr_char] == 0) return RAISE_PARSE_ERROR;
                                    /* The ML code raises Parse_error */
        env[env_curr_char] = -1;
        cmd = loop; break;
      }
      // Fall through
    case 8://shift:
      env[env_curr_char] = -1;
      if (errflag > 0) errflag--;
      // Fall through
    case 9://shift_recover:
      state = tables.table[n2];
      sp++;
      if (sp >= env[env_stacksize]) {
        res = GROW_STACKS_1;
        break exit;
      }
      // Fall through
                                   /* The ML code resizes the stacks */
    case 2://STACKS_GROWN_1:
      env[env_s_stack][sp + 1] = state;
      env[env_v_stack][sp + 1] = env[env_lval];
      env[env_symb_start_stack][sp + 1] = env[env_symb_start];
      env[env_symb_end_stack][sp + 1] = env[env_symb_end];
      cmd = loop;
      break;

    case 10://reduce:
      var m = tables.len[n];
      env[env_asp] = sp;
      env[env_rule_number] = n;
      env[env_rule_len] = m;
      sp = sp - m + 1;
      m = tables.lhs[n];
      state1 = env[env_s_stack][sp];
      n1 = tables.gindex[m];
      n2 = n1 + state1;
      if (n1 != 0 && n2 >= 0 && n2 <= tables[tbl_tablesize] &&
          tables.check[n2] == state1)
        state = tables.table[n2];
      else
        state = tables.dgoto[m];
      if (sp >= env[env_stacksize]) {
        res = GROW_STACKS_2;
        break exit;
      }
      // Fall through
                                  /* The ML code resizes the stacks */
    case 3://STACKS_GROWN_2:
      res = COMPUTE_SEMANTIC_ACTION;
      break exit;
                                  /* The ML code calls the semantic action */
    case 4://SEMANTIC_ACTION_COMPUTED:
      env[env_s_stack][sp + 1] = state;
      env[env_v_stack][sp + 1] = arg;
      var asp = env[env_asp];
      env[env_symb_end_stack][sp + 1] = env[env_symb_end_stack][asp + 1];
      if (sp > asp) {
        /* This is an epsilon production. Take symb_start equal to symb_end. */
        env[env_symb_start_stack][sp + 1] = env[env_symb_end_stack][asp + 1];
      }
      cmd = loop; break;
                                  /* Should not happen */
    default:
      return RAISE_PARSE_ERROR;
    }
  }
  // SAVE
  env[env_sp] = sp;
  env[env_state] = state;
  env[env_errflag] = errflag;
  return res;
}

//Provides: caml_set_parser_trace const
//Dummy function!
function caml_set_parser_trace() { return 0; }

//# 1 "bigarray.js"
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2014 Jérôme Vouillon, Hugo Heuzard, Andy Ray
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
//
// Bigarray.
//
// - all bigarray types including Int64 and Complex.
// - fortran + c layouts
// - sub/slice/reshape
// - retain fast path for 1d array access
//
// Note; int64+complex support if provided by allocating a second TypedArray
// Note; accessor functions are selected when the bigarray is created.  It is assumed
//       that this results in just a function pointer and will thus be fast.

//Provides: caml_ba_init const
function caml_ba_init() {
    return 0;
}

//Provides: caml_ba_init_views
//Requires: caml_ba_views
function caml_ba_init_views() {
    if (!caml_ba_views) {
        var g = joo_global_object;
        caml_ba_views = [
            [
                g.Float32Array, g.Float64Array, g.Int8Array, g.Uint8Array,
                g.Int16Array, g.Uint16Array, g.Int32Array, g.Int32Array,
                g.Int32Array, g.Int32Array, g.Float32Array, g.Float64Array, g.Uint8Array],
            [
                0 /* General */, 0 /* General */, 0 /* General */, 0 /* General */,
                0 /* General */, 0 /* General */, 0 /* General */, 1 /* Int64 */,
                0 /* General */, 0 /* General */, 2 /* Complex */, 2 /* Complex */, 0 /* General */]
        ];
    }
}

//Provides: caml_ba_get_size
//Requires: caml_invalid_argument
function caml_ba_get_size(dims) {
    var n_dims = dims.length;
    var size = 1;
    for (var i = 0; i < n_dims; i++) {
        if (dims[i] < 0)
            caml_invalid_argument("Bigarray.create: negative dimension");
        size = size * dims[i];
    }
    return size;
}

//Provides: caml_ba_views
var caml_ba_views;

//Provides: caml_ba_create_from
//Requires: caml_ba_get_size
//Requires: caml_invalid_argument
//Requires: caml_array_bound_error
function caml_ba_create_from(data, data2, data_type, kind, layout, dims) {
    var n_dims = dims.length;
    var size = caml_ba_get_size(dims);

    //
    // Functions to compute the offsets for C or Fortran layout arrays
    // from the given array of indices.
    //
    function offset_c(index) {
        var ofs = 0;
        if (n_dims != index.length)
            caml_invalid_argument("Bigarray.get/set: bad number of dimensions");
        for (var i = 0; i < n_dims; i++) {
            if (index[i] < 0 || index[i] >= dims[i])
                caml_array_bound_error();
            ofs = (ofs * dims[i]) + index[i];
        }
        return ofs;
    }

    function offset_fortran(index) {
        var ofs = 0;
        if (n_dims != index.length)
            caml_invalid_argument("Bigarray.get/set: wrong number of indices");
        for (var i = n_dims - 1; i >= 0; i--) {
            if (index[i] < 1 || index[i] > dims[i])
                caml_array_bound_error();
            ofs = (ofs * dims[i]) + (index[i] - 1);
        }
        return ofs;
    }

    var offset = layout == 0 ? offset_c : offset_fortran;

    var dim0 = dims[0];

    //
    // Element get functions.
    //
    function get_std(index) {
        var ofs = offset(index);
        var v = data[ofs];
        return v;
    }

    function get_int64(index) {
        var off = offset(index);
        var l = data[off];
        var h = data2[off];
        return [
            255,
            l & 0xffffff,
            ((l >>> 24) & 0xff) | ((h & 0xffff) << 8),
            (h >>> 16) & 0xffff];
    }

    function get_complex(index) {
        var off = offset(index);
        var r = data[off];
        var i = data2[off];
        return [254, r, i];
    }

    var get = data_type == 1 /* Int64 */ ? get_int64 : (data_type == 2 /* Complex */ ? get_complex : get_std);

    function get1_c(i) {
        if (i < 0 || i >= dim0)
            caml_array_bound_error();
        return data[i];
    }
    function get1_fortran(i) {
        if (i < 1 || i > dim0)
            caml_array_bound_error();
        return data[i - 1];
    }
    function get1_any(i) {
        return get([i]);
    }

    var get1 = data_type == 0 /* General */ ? (layout == 0 ? get1_c : get1_fortran) : get1_any;

    //
    // Element set functions
    //
    function set_std_raw(off, v) {
        data[off] = v;
    }

    function set_int64_raw(off, v) {
        data[off] = v[1] | ((v[2] & 0xff) << 24);
        data2[off] = ((v[2] >>> 8) & 0xffff) | (v[3] << 16);
    }

    function set_complex_raw(off, v) {
        data[off] = v[1];
        data2[off] = v[2];
    }

    function set_std(index, v) {
        var ofs = offset(index);
        return set_std_raw(ofs, v);
    }
    function set_int64(index, v) {
        return set_int64_raw(offset(index), v);
    }
    function set_complex(index, v) {
        return set_complex_raw(offset(index), v);
    }

    var set = data_type == 1 /* Int64 */ ? set_int64 : (data_type == 2 /* Complex */ ? set_complex : set_std);

    function set1_c(i, v) {
        if (i < 0 || i >= dim0)
            caml_array_bound_error();
        data[i] = v;
    }
    function set1_fortran(i, v) {
        if (i < 1 || i > dim0)
            caml_array_bound_error();
        data[i - 1] = v;
    }
    function set1_any(i, v) {
        set([i], v);
    }

    var set1 = data_type == 0 /* General */ ? (layout == 0 ? set1_c : set1_fortran) : set1_any;

    //
    // other
    //
    function nth_dim(i) {
        if (i < 0 || i >= n_dims)
            caml_invalid_argument("Bigarray.dim");
        return dims[i];
    }

    function fill(v) {
        if (data_type == 0 /* General */)
            for (var i = 0; i < data.length; i++)
                set_std_raw(i, v);
        if (data_type == 1 /* Int64 */)
            for (var i = 0; i < data.length; i++)
                set_int64_raw(i, v);
        if (data_type == 2 /* Complex */)
            for (var i = 0; i < data.length; i++)
                set_complex_raw(i, v);
    }
    function blit(from) {
        if (n_dims != from.num_dims)
            caml_invalid_argument("Bigarray.blit: dimension mismatch");
        for (var i = 0; i < n_dims; i++)
            if (dims[i] != from.nth_dim(i))
                caml_invalid_argument("Bigarray.blit: dimension mismatch");
        data.set(from.data);
        if (data_type != 0 /* General */)
            data2.set(from.data2);
    }

    function sub(ofs, len) {
        var changed_dim;
        var mul = 1;

        if (layout == 0) {
            for (var i = 1; i < n_dims; i++)
                mul = mul * dims[i];
            changed_dim = 0;
        } else {
            for (var i = 0; i < (n_dims - 1); i++)
                mul = mul * dims[i];
            changed_dim = n_dims - 1;
            ofs = ofs - 1;
        }

        if (ofs < 0 || len < 0 || (ofs + len) > dims[changed_dim])
            caml_invalid_argument("Bigarray.sub: bad sub-array");

        var new_data = data.subarray(ofs * mul, (ofs + len) * mul);
        var new_data2 = data_type == 0 /* General */ ? null : data2.subarray(ofs * mul, (ofs + len) * mul);

        var new_dims = [];
        for (var i = 0; i < n_dims; i++)
            new_dims[i] = dims[i];
        new_dims[changed_dim] = len;

        return caml_ba_create_from(new_data, new_data2, data_type, kind, layout, new_dims);
    }

    function slice(vind) {
        var num_inds = vind.length;
        var index = [];
        var sub_dims = [];
        var ofs;

        if (num_inds >= n_dims)
            caml_invalid_argument("Bigarray.slice: too many indices");

        // Compute offset and check bounds
        if (layout == 0) {
            for (var i = 0; i < num_inds; i++)
                index[i] = vind[i];
            for (; i < n_dims; i++)
                index[i] = 0;
            ofs = offset(index);
            sub_dims = dims.slice(num_inds);
        } else {
            for (var i = 0; i < num_inds; i++)
                index[n_dims - num_inds + i] = vind[i];
            for (var i = 0; i < n_dims - num_inds; i++)
                index[i] = 1;
            ofs = offset(index);
            sub_dims = dims.slice(0, num_inds);
        }

        var size = caml_ba_get_size(sub_dims);
        var new_data = data.subarray(ofs, ofs + size);
        var new_data2 = data_type == 0 /* General */ ? null : data2.subarray(ofs, ofs + size);

        return caml_ba_create_from(new_data, new_data2, data_type, kind, layout, sub_dims);
    }

    function reshape(vdim) {
        var new_dim = [];
        var num_dims = vdim.length;

        if (num_dims < 1)
            caml_invalid_argument("Bigarray.reshape: bad number of dimensions");
        var num_elts = 1;
        for (var i = 0; i < num_dims; i++) {
            new_dim[i] = vdim[i];
            if (new_dim[i] < 0)
                caml_invalid_argument("Bigarray.reshape: negative dimension");
            num_elts = num_elts * new_dim[i];
        }

        // Check that sizes agree
        if (num_elts != size)
            caml_invalid_argument("Bigarray.reshape: size mismatch");

        return caml_ba_create_from(data, data2, data_type, kind, layout, new_dim);
    }

    function compare(b, total) {
        if (layout != b.layout)
            return b.layout - layout;
        if (n_dims != b.num_dims)
            return b.num_dims - n_dims;
        for (var i = 0; i < n_dims; i++)
            if (nth_dim(i) != b.nth_dim(i))
                return (nth_dim(i) < b.nth_dim(i)) ? -1 : 1;
        switch (kind) {
            case 0:
            case 1:
            case 10:
            case 11:
                var x, y;
                for (var i = 0; i < data.length; i++) {
                    x = data[i];
                    y = b.data[i];

                    //first array
                    if (x < y)
                        return -1;
                    if (x > y)
                        return 1;
                    if (x != y) {
                        if (x != y) {
                            if (!total)
                                return NaN;
                            if (x == x)
                                return 1;
                            if (y == y)
                                return -1;
                        }
                    }
                    if (data2) {
                        //second array
                        x = data2[i];
                        y = b.data2[i];
                        if (x < y)
                            return -1;
                        if (x > y)
                            return 1;
                        if (x != y) {
                            if (x != y) {
                                if (!total)
                                    return NaN;
                                if (x == x)
                                    return 1;
                                if (y == y)
                                    return -1;
                            }
                        }
                    }
                }
                ;
                break;

            case 2:
            case 3:
            case 4:
            case 5:
            case 6:
            case 8:
            case 9:
            case 12:
                for (var i = 0; i < data.length; i++) {
                    if (data[i] < b.data[i])
                        return -1;
                    if (data[i] > b.data[i])
                        return 1;
                }
                ;
                break;

            case 7:
                for (var i = 0; i < data.length; i++) {
                    if (data2[i] < b.data2[i])
                        return -1;
                    if (data2[i] > b.data2[i])
                        return 1;
                    if (data[i] < b.data[i])
                        return -1;
                    if (data[i] > b.data[i])
                        return 1;
                }
                ;
                break;
        }
        return 0;
    }

    return {
        data: data,
        data2: data2,
        data_type: data_type,
        num_dims: n_dims,
        nth_dim: nth_dim,
        kind: kind,
        layout: layout,
        size: size,
        sub: sub,
        slice: slice,
        blit: blit,
        fill: fill,
        reshape: reshape,
        get: get,
        get1: get1,
        set: set,
        set1: set1,
        compare: compare
    };
}

//Provides: caml_ba_create
//Requires: caml_ba_create_from
//Requires: caml_js_from_array
//Requires: caml_ba_views
//Requires: caml_ba_init_views
//Requires: caml_invalid_argument
//Requires: caml_ba_get_size
function caml_ba_create(kind, layout, dims_ml) {
    // Initialize TypedArray views
    caml_ba_init_views();

    // set up dimensions and calculate size
    var dims = caml_js_from_array(dims_ml);

    //var n_dims = dims.length;
    var size = caml_ba_get_size(dims);

    // Allocate TypedArray
    var view = caml_ba_views[0][kind];
    if (!view)
        caml_invalid_argument("Bigarray.create: unsupported kind");
    var data = new view(size);

    // 2nd TypedArray for int64, complex32 and complex64
    var data_type = caml_ba_views[1][kind];
    var data2 = null;
    if (data_type != 0 /* General */) {
        data2 = new view(size);
    }

    return caml_ba_create_from(data, data2, data_type, kind, layout, dims);
}

//Provides: caml_ba_change_layout
//Requires: caml_ba_create_from
function caml_ba_change_layout(ba, layout) {
  if(ba.layout == layout) return ba;
  var dims = [];
  for(var i = 0; i < ba.num_dims; i++)
    dims[i] = ba.nth_dim(i);
  return caml_ba_create_from(ba.data, ba.data2, ba.data_type, ba.kind, layout, dims);
}

//Provides: caml_ba_kind
function caml_ba_kind(ba) {
    return ba.kind;
}

//Provides: caml_ba_layout
function caml_ba_layout(ba) {
    return ba.layout;
}

//Provides: caml_ba_num_dims
function caml_ba_num_dims(ba, _dim) {
    return ba.num_dims;
}

//Provides: caml_ba_dim
function caml_ba_dim(ba, dim) {
    return ba.nth_dim(dim);
}

//Provides: caml_ba_dim_1
function caml_ba_dim_1(ba) {
    return ba.nth_dim(0);
}

//Provides: caml_ba_dim_2
function caml_ba_dim_2(ba) {
    return ba.nth_dim(1);
}

//Provides: caml_ba_dim_3
function caml_ba_dim_3(ba) {
    return ba.nth_dim(2);
}

//Provides: caml_ba_get_generic
//Requires: caml_js_from_array
function caml_ba_get_generic(ba, index) {
    return ba.get(caml_js_from_array(index));
}

//Provides: caml_ba_uint8_get16
function caml_ba_uint8_get16(ba, i0) {
    var b1 = ba.get1(i0);
    var b2 = ba.get1(i0+1) << 8;
    return (b1 | b2);
}

//Provides: caml_ba_uint8_get32
function caml_ba_uint8_get32(ba, i0) {
    var b1 = ba.get1(i0);
    var b2 = ba.get1(i0+1) << 8;
    var b3 = ba.get1(i0+2) << 16;
    var b4 = ba.get1(i0+3) << 24;
    return (b1 | b2 | b3 | b4);
}

//Provides: caml_ba_uint8_get64
function caml_ba_uint8_get64(ba, i0) {
    var b1 = ba.get1(i0);
    var b2 = ba.get1(i0+1) << 8;
    var b3 = ba.get1(i0+2) << 16;
    var b4 = ba.get1(i0+3);
    var b5 = ba.get1(i0+4) << 8;
    var b6 = ba.get1(i0+5) << 16;
    var b7 = ba.get1(i0+6);
    var b8 = ba.get1(i0+7) << 8;
    return [255, b1 | b2 | b3, b4 | b5 | b6, b7 | b8 ];
}

//Provides: caml_ba_get_1
function caml_ba_get_1(ba, i0) {
    return ba.get1(i0);
}

//Provides: caml_ba_get_2
function caml_ba_get_2(ba, i0, i1) {
    return ba.get([i0, i1]);
}

//Provides: caml_ba_get_3
function caml_ba_get_3(ba, i0, i1, i2) {
    return ba.get([i0, i1, i2]);
}

//Provides: caml_ba_set_generic
//Requires: caml_js_from_array
function caml_ba_set_generic(ba, index, v) {
    return ba.set(caml_js_from_array(index), v);
}

//Provides: caml_ba_uint8_set16
function caml_ba_uint8_set16(ba, i0, v) {
    ba.set1(i0, v & 0xff);
    ba.set1(i0+1, (v >>> 8) & 0xff);
    return 0;
}

//Provides: caml_ba_uint8_set32
function caml_ba_uint8_set32(ba, i0, v) {
    ba.set1(i0, v & 0xff);
    ba.set1(i0+1, (v >>> 8) & 0xff);
    ba.set1(i0+2, (v >>> 16) & 0xff);
    ba.set1(i0+3, (v >>> 24) & 0xff);
    return 0;
}

//Provides: caml_ba_uint8_set64
function caml_ba_uint8_set64(ba, i0, v) {
    ba.set1(i0, v[1] & 0xff);
    ba.set1(i0+1, (v[1] >> 8) & 0xff);
    ba.set1(i0+2, v[1] >> 16);
    ba.set1(i0+3, v[2] & 0xff);
    ba.set1(i0+4, (v[2] >> 8) & 0xff);
    ba.set1(i0+5, v[2] >> 16);
    ba.set1(i0+6, v[3] & 0xff);
    ba.set1(i0+7, v[3] >> 8);
    return 0;
}

//Provides: caml_ba_set_1
function caml_ba_set_1(ba, i0, v) {
    return ba.set1(i0, v);
}

//Provides: caml_ba_set_2
function caml_ba_set_2(ba, i0, i1, v) {
    return ba.set([i0, i1], v);
}

//Provides: caml_ba_set_3
function caml_ba_set_3(ba, i0, i1, i2, v) {
    return ba.set([i0, i1, i2], v);
}

//Provides: caml_ba_blit
function caml_ba_blit(src, dst) {
    dst.blit(src);
    return 0;
}

//Provides: caml_ba_fill
function caml_ba_fill(ba, init) {
    ba.fill(init);
    return 0;
}

//Provides: caml_ba_sub
function caml_ba_sub(ba, ofs, len) {
    return ba.sub(ofs, len);
}

//Provides: caml_ba_slice
//Requires: caml_js_from_array
function caml_ba_slice(ba, vind) {
    return ba.slice(caml_js_from_array(vind));
}

//Provides: caml_ba_reshape
//Requires: caml_js_from_array
function caml_ba_reshape(ba, vind) {
    return ba.reshape(caml_js_from_array(vind));
}

//# 1 "unix.js"
//Provides: unix_gettimeofday
function unix_gettimeofday () {
  return (new Date()).getTime() / 1000;
}

//Provides: unix_time
//Requires: unix_gettimeofday
function unix_time () {
  return Math.floor(unix_gettimeofday ());
}

//Provides: unix_gmtime
function unix_gmtime (t) {
  var d = new Date (t * 1000);
  var januaryfirst = new Date(Date.UTC(d.getUTCFullYear(), 0, 1));
  var doy = Math.floor((d - januaryfirst) / 86400000);
  return [0, d.getUTCSeconds(), d.getUTCMinutes(), d.getUTCHours(),
          d.getUTCDate(), d.getUTCMonth(), d.getUTCFullYear() - 1900,
          d.getUTCDay(), doy,
          false | 0 /* for UTC daylight savings time is false */]
}

//Provides: unix_localtime
function unix_localtime (t) {
  var d = new Date (t * 1000);
  var januaryfirst = new Date(d.getFullYear(), 0, 1);
  var doy = Math.floor((d - januaryfirst) / 86400000);
  var jan = new Date(d.getFullYear(), 0, 1);
  var jul = new Date(d.getFullYear(), 6, 1);
  var stdTimezoneOffset = Math.max(jan.getTimezoneOffset(), jul.getTimezoneOffset());
  return [0, d.getSeconds(), d.getMinutes(), d.getHours(),
  d.getDate(), d.getMonth(), d.getFullYear() - 1900,
  d.getDay(), doy,
  (d.getTimezoneOffset() < stdTimezoneOffset) | 0 /* daylight savings time  field. */]
}

//Provides: unix_mktime
//Requires: unix_localtime
function unix_mktime(tm){
    var d = new Date(tm[6]+1900,tm[5],tm[4],tm[3],tm[2],tm[1]);
    var t = Math.floor(d.getTime() / 1000);
    var tm2 = unix_localtime(t);
    return [0,t,tm2];
}

//Provides: win_startup const
function win_startup() {}

//Provides: win_cleanup const
function win_cleanup() {}

//Provides: win_handle_fd const
function win_handle_fd(x) {return x;}

//# 1 "stdlib.js"
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

///////////// Core

//Provides: raw_array_sub
function raw_array_sub (a,i,l) {
  var b = new Array(l);
  for(var j = 0; j < l; j++) b[j] = a[i+j];
  return b
}

//Provides: raw_array_copy
function raw_array_copy (a) {
  var l = a.length;
  var b = new Array(l);
  for(var i = 0; i < l; i++ ) b[i] = a[i];
  return b
}

//Provides: raw_array_cons
function raw_array_cons (a,x) {
  var l = a.length;
  var b = new Array(l+1);
  b[0]=x;
  for(var i = 1; i <= l; i++ ) b[i] = a[i-1];
  return b
}

//Provides: raw_array_append_one
function raw_array_append_one(a,x) {
  var l = a.length;
  var b = new Array(l+1);
  var i = 0;
  for(; i < l; i++ ) b[i] = a[i];
  b[i]=x;
  return b
}

//Provides: caml_call_gen (const, shallow)
//Requires: raw_array_sub
//Requires: raw_array_append_one
function caml_call_gen(f, args) {
  if(f.fun)
    return caml_call_gen(f.fun, args);
  var n = f.length;
  var argsLen = args.length;
  var d = n - argsLen;
  if (d == 0)
    return f.apply(null, args);
  else if (d < 0)
    return caml_call_gen(f.apply(null,
                                 raw_array_sub(args,0,n)),
                         raw_array_sub(args,n,argsLen - n));
  else
    return function (x){ return caml_call_gen(f, raw_array_append_one(args,x)); };
}

//Provides: caml_named_values
var caml_named_values = {};

//Provides: caml_register_named_value (const,const)
//Requires: caml_named_values, caml_jsbytes_of_string
function caml_register_named_value(nm,v) {
  caml_named_values[caml_jsbytes_of_string(nm)] = v;
  return 0;
}

//Provides: caml_named_value
//Requires: caml_named_values
function caml_named_value(nm) {
  return caml_named_values[nm]
}

//Provides: caml_global_data
var caml_global_data = [0];

//Provides: caml_register_global (const, shallow, const)
//Requires: caml_global_data
function caml_register_global (n, v, name_opt) {
  caml_global_data[n + 1] = v;
  if(name_opt) caml_global_data[name_opt] = v;
}

//Provides: caml_get_global_data mutable
//Requires: caml_global_data
function caml_get_global_data () { return caml_global_data; }

//Raise exception


//Provides: caml_raise_constant (const)
//Version: < 4.02
function caml_raise_constant (tag) { throw [0, tag]; }

//Provides: caml_raise_constant (const)
//Version: >= 4.02
function caml_raise_constant (tag) { throw tag; }

//Provides: caml_return_exn_constant (const)
//Version: < 4.02
function caml_return_exn_constant (tag) { return [0, tag]; }

//Provides: caml_return_exn_constant (const)
//Version: >= 4.02
function caml_return_exn_constant (tag) { return tag; }

//Provides: caml_raise_with_arg (const, const)
function caml_raise_with_arg (tag, arg) { throw [0, tag, arg]; }

//Provides: caml_raise_with_string (const, const)
//Requires: caml_raise_with_arg,caml_new_string
function caml_raise_with_string (tag, msg) {
  caml_raise_with_arg (tag, caml_new_string (msg));
}

//Provides: caml_raise_sys_error (const)
//Requires: caml_raise_with_string, caml_global_data
function caml_raise_sys_error (msg) {
  caml_raise_with_string(caml_global_data.Sys_error, msg);
}

//Provides: caml_failwith (const)
//Requires: caml_raise_with_string, caml_global_data
function caml_failwith (msg) {
  caml_raise_with_string(caml_global_data.Failure, msg);
}

//Provides: caml_wrap_exception const (const)
//Requires: caml_global_data,caml_js_to_string,caml_named_value
//Requires: caml_return_exn_constant
function caml_wrap_exception(e) {
  if(e instanceof Array) return e;
  //Stack_overflow: chrome, safari
  if(joo_global_object.RangeError
     && e instanceof joo_global_object.RangeError
     && e.message
     && e.message.match(/maximum call stack/i))
    return caml_return_exn_constant(caml_global_data.Stack_overflow);
  //Stack_overflow: firefox
  if(joo_global_object.InternalError
     && e instanceof joo_global_object.InternalError
     && e.message
     && e.message.match(/too much recursion/i))
    return caml_return_exn_constant(caml_global_data.Stack_overflow);
  //Wrap Error in Js.Error exception
  if(e instanceof joo_global_object.Error && caml_named_value("jsError"))
    return [0,caml_named_value("jsError"),e];
  //fallback: wrapped in Failure
  return [0,caml_global_data.Failure,caml_js_to_string (String(e))];
}

// Experimental
//Provides: caml_exn_with_js_backtrace
//Requires: caml_global_data
function caml_exn_with_js_backtrace(exn, force) {
    //never reraise for constant exn
    if(!exn.js_error || force || exn[0] == 248) exn.js_error = new joo_global_object.Error("Js exception containing backtrace");
  return exn;
}
//Provides: caml_js_error_of_exception
function caml_js_error_of_exception(exn) {
  if(exn.js_error) { return exn.js_error; }
  return null;
}

//Provides: caml_invalid_argument (const)
//Requires: caml_raise_with_string, caml_global_data
function caml_invalid_argument (msg) {
  caml_raise_with_string(caml_global_data.Invalid_argument, msg);
}

//Provides: caml_raise_end_of_file
//Requires: caml_raise_constant, caml_global_data
function caml_raise_end_of_file () {
  caml_raise_constant(caml_global_data.End_of_file);
}

//Provides: caml_raise_zero_divide
//Requires: caml_raise_constant, caml_global_data
function caml_raise_zero_divide () {
  caml_raise_constant(caml_global_data.Division_by_zero);
}

//Provides: caml_raise_not_found
//Requires: caml_raise_constant, caml_global_data
function caml_raise_not_found () {
  caml_raise_constant(caml_global_data.Not_found); }


//Provides: caml_array_bound_error
//Requires: caml_invalid_argument
function caml_array_bound_error () {
  caml_invalid_argument("index out of bounds");
}

//Provides: caml_update_dummy
function caml_update_dummy (x, y) {
  if( typeof y==="function" ) { x.fun = y; return 0; }
  if( y.fun ) { x.fun = y.fun; return 0; }
  var i = y.length; while (i--) x[i] = y[i]; return 0;
}

//Provides: caml_obj_is_block const (const)
function caml_obj_is_block (x) { return +(x instanceof Array); }
//Provides: caml_obj_tag const (const)
//Requires: MlBytes
function caml_obj_tag (x) { return (x instanceof Array)?x[0]:(x instanceof MlBytes)?252:1000; }
//Provides: caml_obj_set_tag (mutable, const)
function caml_obj_set_tag (x, tag) { x[0] = tag; return 0; }
//Provides: caml_obj_block const (const,const)
function caml_obj_block (tag, size) {
  var o = new Array(size+1);
  o[0]=tag;
  for (var i = 1; i <= size; i++) o[i] = 0;
  return o;
}
//Provides: caml_obj_dup mutable (const)
function caml_obj_dup (x) {
  var l = x.length;
  var a = new Array(l);
  for(var i = 0; i < l; i++ ) a[i] = x[i];
  return a;
}
//Provides: caml_obj_truncate (mutable, const)
//Requires: caml_invalid_argument
function caml_obj_truncate (x, s) {
  if (s<=0 || s + 1 > x.length)
    caml_invalid_argument ("Obj.truncate");
  if (x.length != s + 1) x.length = s + 1;
  return 0;
}

//Provides: caml_lazy_make_forward const (const)
function caml_lazy_make_forward (v) { return [250, v]; }

//Provides: caml_mul const
if (!Math.imul)
  Math.imul =
    function (x,y)
    { y |= 0; return ((((x >> 16) * y) << 16) + (x & 0xffff) * y)|0; };
var caml_mul = Math.imul;

//slightly slower
// function mul32(x,y) {
//   var xlo = x & 0xffff;
//   var xhi = x - xlo;
//   return (((xhi * y) |0) + xlo * y)|0;
// }

//Provides: caml_div
//Requires: caml_raise_zero_divide
function caml_div(x,y) {
  if (y == 0) caml_raise_zero_divide ();
  return (x/y)|0;
}

//Provides: caml_mod
//Requires: caml_raise_zero_divide
function caml_mod(x,y) {
  if (y == 0) caml_raise_zero_divide ();
  return x%y;
}

///////////// Pervasive
//Provides: caml_array_set (mutable, const, const)
//Requires: caml_array_bound_error
function caml_array_set (array, index, newval) {
  if ((index < 0) || (index >= array.length - 1)) caml_array_bound_error();
  array[index+1]=newval; return 0;
}

//Provides: caml_array_get mutable (const, const)
//Requires: caml_array_bound_error
function caml_array_get (array, index) {
  if ((index < 0) || (index >= array.length - 1)) caml_array_bound_error();
  return array[index+1];
}

//Provides: caml_check_bound (const, const)
//Requires: caml_array_bound_error
function caml_check_bound (array, index) {
  if (index >>> 0 >= array.length - 1) caml_array_bound_error();
  return array;
}

//Provides: caml_make_vect const (const, const)
function caml_make_vect (len, init) {
  var len = len + 1 | 0;
  var b = new Array(len);
  b[0]=0;
  for (var i = 1; i < len; i++) b[i] = init;
  return b;
}

//Provides: caml_make_float_vect const (const)
function caml_make_float_vect(len){
  var len = len + 1 | 0;
  var b = new Array(len);
  b[0]=254;
  for (var i = 1; i < len; i++) b[i] = 0;
  return b
}
//Provides: caml_floatarray_create const (const)
function caml_floatarray_create(len){
  var len = len + 1 | 0;
  var b = new Array(len);
  b[0]=254;
  for (var i = 1; i < len; i++) b[i] = 0;
  return b
}

//Provides: caml_compare_val (const, const, const)
//Requires: MlBytes, caml_int64_compare, caml_int_compare, caml_string_compare
//Requires: caml_invalid_argument
function caml_compare_val (a, b, total) {
  var stack = [];
  for(;;) {
    if (!(total && a === b)) {
      if (a instanceof MlBytes) {
        if (b instanceof MlBytes) {
            if (a !== b) {
		var x = caml_string_compare(a, b);
		if (x != 0) return x;
	    }
        } else
          // Should not happen
          return 1;
      } else if (a instanceof Array && a[0] === (a[0]|0)) {
        var ta = a[0];
        // ignore double_array_tag
        if (ta === 254) ta=0;
        // Forward object
        if (ta === 250) {
          a = a[1];
          continue;
        } else if (b instanceof Array && b[0] === (b[0]|0)) {
          var tb = b[0];
          // ignore double_array_tag
          if (tb === 254) tb=0;
          // Forward object
          if (tb === 250) {
            b = b[1];
            continue;
          } else if (ta != tb) {
            return (ta < tb)?-1:1;
          } else {
            switch (ta) {
            case 248: {
		// Object
		var x = caml_int_compare(a[2], b[2]);
		if (x != 0) return x;
		break;
	    }
            case 251: {
                caml_invalid_argument("equal: abstract value");
            }
            case 255: {
		// Int64
		var x = caml_int64_compare(a, b);
		if (x != 0) return x;
		break;
	    }
            default:
              if (a.length != b.length) return (a.length < b.length)?-1:1;
              if (a.length > 1) stack.push(a, b, 1);
            }
          }
        } else
          return 1;
      } else if (b instanceof MlBytes ||
                 (b instanceof Array && b[0] === (b[0]|0))) {
        return -1;
      } else if (typeof a != "number" && a && a.compare) {
        var cmp = a.compare(b,total);
        if (cmp != 0) return cmp;
      } else if (typeof a == "function") {
        caml_invalid_argument("compare: functional value");
      } else {
        if (a < b) return -1;
        if (a > b) return 1;
        if (a != b) {
          if (!total) return NaN;
          if (a == a) return 1;
          if (b == b) return -1;
        }
      }
    }
    if (stack.length == 0) return 0;
    var i = stack.pop();
    b = stack.pop();
    a = stack.pop();
    if (i + 1 < a.length) stack.push(a, b, i + 1);
    a = a[i];
    b = b[i];
  }
}
//Provides: caml_compare (const, const)
//Requires: caml_compare_val
function caml_compare (a, b) { return caml_compare_val (a, b, true); }
//Provides: caml_int_compare mutable (const, const)
function caml_int_compare (a, b) {
  if (a < b) return (-1); if (a == b) return 0; return 1;
}
//Provides: caml_equal mutable (const, const)
//Requires: caml_compare_val
function caml_equal (x, y) { return +(caml_compare_val(x,y,false) == 0); }
//Provides: caml_notequal mutable (const, const)
//Requires: caml_compare_val
function caml_notequal (x, y) { return +(caml_compare_val(x,y,false) != 0); }
//Provides: caml_greaterequal mutable (const, const)
//Requires: caml_compare_val
function caml_greaterequal (x, y) { return +(caml_compare_val(x,y,false) >= 0); }
//Provides: caml_greaterthan mutable (const, const)
//Requires: caml_compare_val
function caml_greaterthan (x, y) { return +(caml_compare_val(x,y,false) > 0); }
//Provides: caml_lessequal mutable (const, const)
//Requires: caml_compare_val
function caml_lessequal (x, y) { return +(caml_compare_val(x,y,false) <= 0); }
//Provides: caml_lessthan mutable (const, const)
//Requires: caml_compare_val
function caml_lessthan (x, y) { return +(caml_compare_val(x,y,false) < 0); }

//Provides: caml_parse_sign_and_base
//Requires: caml_string_unsafe_get, caml_ml_string_length
function caml_parse_sign_and_base (s) {
  var i = 0, len = caml_ml_string_length(s), base = 10, sign = 1;
  if (len > 0) {
    switch (caml_string_unsafe_get(s,i)) {
    case 45: i++; sign = -1; break;
    case 43: i++; sign = 1; break;
    }
  }
  if (i + 1 < len && caml_string_unsafe_get(s, i) == 48)
    switch (caml_string_unsafe_get(s, i + 1)) {
    case 120: case 88: base = 16; i += 2; break;
    case 111: case 79: base =  8; i += 2; break;
    case  98: case 66: base =  2; i += 2; break;
    }
  return [i, sign, base];
}

//Provides: caml_parse_digit
function caml_parse_digit(c) {
  if (c >= 48 && c <= 57)  return c - 48;
  if (c >= 65 && c <= 90)  return c - 55;
  if (c >= 97 && c <= 122) return c - 87;
  return -1;
}

//Provides: caml_int_of_string (const)
//Requires: caml_ml_string_length, caml_string_unsafe_get
//Requires: caml_parse_sign_and_base, caml_parse_digit, caml_failwith
function caml_int_of_string (s) {
  var r = caml_parse_sign_and_base (s);
  var i = r[0], sign = r[1], base = r[2];
  var len = caml_ml_string_length(s);
  var threshold = -1 >>> 0;
  var c = (i < len)?caml_string_unsafe_get(s, i):0;
  var d = caml_parse_digit(c);
  if (d < 0 || d >= base) caml_failwith("int_of_string");
  var res = d;
  for (i++;i<len;i++) {
    c = caml_string_unsafe_get(s, i);
    if (c == 95) continue;
    d = caml_parse_digit(c);
    if (d < 0 || d >= base) break;
    res = base * res + d;
    if (res > threshold) caml_failwith("int_of_string");
  }
  if (i != len) caml_failwith("int_of_string");
  // For base different from 10, we expect an unsigned representation,
  // hence any value of 'res' (less than 'threshold') is acceptable.
  // But we have to convert the result back to a signed integer.
  res = sign * res;
  if ((base == 10) && ((res | 0) != res))
    /* Signed representation expected, allow -2^(nbits-1) to 2^(nbits-1) - 1 */
    caml_failwith("int_of_string");
  return res | 0;
}

//Provides: caml_float_of_string (const)
//Requires: caml_failwith, caml_jsbytes_of_string
function caml_float_of_string(s) {
  var res;
  s = caml_jsbytes_of_string (s);
  res = +s;
  if ((s.length > 0) && (res === res)) return res;
  s = s.replace(/_/g,"");
  res = +s;
  if (((s.length > 0) && (res === res)) || /^[+-]?nan$/i.test(s)) return res;
  var m = /^ *([+-]?)0x([0-9a-f]+)\.?([0-9a-f]*)p([+-]?[0-9]+)/i.exec(s);
//            1        2             3           4
  if(m){
    var m3 = m[3].replace(/0+$/,'');
    var mantissa = parseInt(m[1] + m[2] + m3, 16);
    var exponent = (m[4]|0) - 4*m3.length;
    res = mantissa * Math.pow(2, exponent);
    return res;
  }
  if(/^\+?inf(inity)?$/i.test(s)) return Infinity;
  if(/^-inf(inity)?$/i.test(s)) return -Infinity;
  caml_failwith("float_of_string");
}

//Provides: caml_is_printable const (const)
function caml_is_printable(c) { return +(c > 31 && c < 127); }

///////////// Format
//Provides: caml_parse_format
//Requires: caml_jsbytes_of_string, caml_invalid_argument
function caml_parse_format (fmt) {
  fmt = caml_jsbytes_of_string(fmt);
  var len = fmt.length;
  if (len > 31) caml_invalid_argument("format_int: format too long");
  var f =
    { justify:'+', signstyle:'-', filler:' ', alternate:false,
      base:0, signedconv:false, width:0, uppercase:false,
      sign:1, prec:-1, conv:'f' };
  for (var i = 0; i < len; i++) {
    var c = fmt.charAt(i);
    switch (c) {
    case '-':
      f.justify = '-'; break;
    case '+': case ' ':
      f.signstyle = c; break;
    case '0':
      f.filler = '0'; break;
    case '#':
      f.alternate = true; break;
    case '1': case '2': case '3': case '4': case '5':
    case '6': case '7': case '8': case '9':
      f.width = 0;
      while (c=fmt.charCodeAt(i) - 48, c >= 0 && c <= 9) {
        f.width = f.width * 10 + c; i++
      }
      i--;
     break;
    case '.':
      f.prec = 0;
      i++;
      while (c=fmt.charCodeAt(i) - 48, c >= 0 && c <= 9) {
        f.prec = f.prec * 10 + c; i++
      }
      i--;
    case 'd': case 'i':
      f.signedconv = true; /* fallthrough */
    case 'u':
      f.base = 10; break;
    case 'x':
      f.base = 16; break;
    case 'X':
      f.base = 16; f.uppercase = true; break;
    case 'o':
      f.base = 8; break;
    case 'e': case 'f': case 'g':
      f.signedconv = true; f.conv = c; break;
    case 'E': case 'F': case 'G':
      f.signedconv = true; f.uppercase = true;
      f.conv = c.toLowerCase (); break;
    }
  }
  return f;
}

//Provides: caml_finish_formatting
//Requires: caml_new_string
function caml_finish_formatting(f, rawbuffer) {
  if (f.uppercase) rawbuffer = rawbuffer.toUpperCase();
  var len = rawbuffer.length;
  /* Adjust len to reflect additional chars (sign, etc) */
  if (f.signedconv && (f.sign < 0 || f.signstyle != '-')) len++;
  if (f.alternate) {
    if (f.base == 8) len += 1;
    if (f.base == 16) len += 2;
  }
  /* Do the formatting */
  var buffer = "";
  if (f.justify == '+' && f.filler == ' ')
    for (var i = len; i < f.width; i++) buffer += ' ';
  if (f.signedconv) {
    if (f.sign < 0) buffer += '-';
    else if (f.signstyle != '-') buffer += f.signstyle;
  }
  if (f.alternate && f.base == 8) buffer += '0';
  if (f.alternate && f.base == 16) buffer += "0x";
  if (f.justify == '+' && f.filler == '0')
    for (var i = len; i < f.width; i++) buffer += '0';
  buffer += rawbuffer;
  if (f.justify == '-')
    for (var i = len; i < f.width; i++) buffer += ' ';
  return caml_new_string (buffer);
}

//Provides: caml_format_int const (const, const)
//Requires: caml_parse_format, caml_finish_formatting, caml_str_repeat
//Requires: caml_new_string, caml_jsbytes_of_string
function caml_format_int(fmt, i) {
  if (caml_jsbytes_of_string(fmt) == "%d") return caml_new_string(""+i);
  var f = caml_parse_format(fmt);
  if (i < 0) { if (f.signedconv) { f.sign = -1; i = -i; } else i >>>= 0; }
  var s = i.toString(f.base);
  if (f.prec >= 0) {
    f.filler = ' ';
    var n = f.prec - s.length;
    if (n > 0) s = caml_str_repeat (n, '0') + s;
  }
  return caml_finish_formatting(f, s);
}

//Provides: caml_format_float const
//Requires: caml_parse_format, caml_finish_formatting
function caml_format_float (fmt, x) {
  var s, f = caml_parse_format(fmt);
  var prec = (f.prec < 0)?6:f.prec;
  if (x < 0 || (x == 0 && 1/x == -Infinity)) { f.sign = -1; x = -x; }
  if (isNaN(x)) { s = "nan"; f.filler = ' '; }
  else if (!isFinite(x)) { s = "inf"; f.filler = ' '; }
  else
    switch (f.conv) {
    case 'e':
      var s = x.toExponential(prec);
      // exponent should be at least two digits
      var i = s.length;
      if (s.charAt(i - 3) == 'e')
        s = s.slice (0, i - 1) + '0' + s.slice (i - 1);
      break;
    case 'f':
      s = x.toFixed(prec); break;
    case 'g':
      prec = prec?prec:1;
      s = x.toExponential(prec - 1);
      var j = s.indexOf('e');
      var exp = +s.slice(j + 1);
      if (exp < -4 || x >= 1e21 || x.toFixed(0).length > prec) {
        // remove trailing zeroes
        var i = j - 1; while (s.charAt(i) == '0') i--;
        if (s.charAt(i) == '.') i--;
        s = s.slice(0, i + 1) + s.slice(j);
        i = s.length;
        if (s.charAt(i - 3) == 'e')
          s = s.slice (0, i - 1) + '0' + s.slice (i - 1);
        break;
      } else {
        var p = prec;
        if (exp < 0) { p -= exp + 1; s = x.toFixed(p); }
        else while (s = x.toFixed(p), s.length > prec + 1) p--;
        if (p) {
          // remove trailing zeroes
          var i = s.length - 1; while (s.charAt(i) == '0') i--;
          if (s.charAt(i) == '.') i--;
          s = s.slice(0, i + 1);
        }
      }
      break;
    }
  return caml_finish_formatting(f, s);
}

///////////// Hashtbl
//Provides: caml_hash_univ_param mutable
//Requires: MlBytes, caml_convert_string_to_bytes
//Requires: caml_int64_to_bytes, caml_int64_bits_of_float
function caml_hash_univ_param (count, limit, obj) {
  var hash_accu = 0;
  function hash_aux (obj) {
    limit --;
    if (count < 0 || limit < 0) return;
    if (obj instanceof Array && obj[0] === (obj[0]|0)) {
      switch (obj[0]) {
      case 248:
        // Object
        count --;
        hash_accu = (hash_accu * 65599 + obj[2]) | 0;
        break;
      case 250:
        // Forward
        limit++; hash_aux(obj); break;
      case 255:
        // Int64
        count --;
        hash_accu = (hash_accu * 65599 + obj[1] + (obj[2] << 24)) | 0;
        break;
      default:
        count --;
        hash_accu = (hash_accu * 19 + obj[0]) | 0;
        for (var i = obj.length - 1; i > 0; i--) hash_aux (obj[i]);
      }
    } else if (obj instanceof MlBytes) {
      count --;
      switch (obj.t & 6) {
      default: /* PARTIAL */
        caml_convert_string_to_bytes(obj);
      case 0: /* BYTES */
        for (var b = obj.c, l = obj.l, i = 0; i < l; i++)
          hash_accu = (hash_accu * 19 + b.charCodeAt(i)) | 0;
        break;
      case 2: /* ARRAY */
        for (var a = obj.c, l = obj.l, i = 0; i < l; i++)
          hash_accu = (hash_accu * 19 + a[i]) | 0;
      }
    } else if (obj === (obj|0)) {
      // Integer
      count --;
      hash_accu = (hash_accu * 65599 + obj) | 0;
    } else if (obj === +obj) {
      // Float
      count--;
      var p = caml_int64_to_bytes (caml_int64_bits_of_float (obj));
      for (var i = 7; i >= 0; i--) hash_accu = (hash_accu * 19 + p[i]) | 0;
    } else if(obj && obj.hash && typeof obj.hash === "function") {
	// Custom
	hash_accu = (hash_accu * 65599 + obj.hash()) | 0;
    }
  }
  hash_aux (obj);
  return hash_accu & 0x3FFFFFFF;
}

//function ROTL32(x,n) { return ((x << n) | (x >>> (32-n))); }
//Provides: caml_hash_mix_int
//Requires: caml_mul
function caml_hash_mix_int(h,d) {
  d = caml_mul(d, 0xcc9e2d51|0);
  d = ((d << 15) | (d >>> (32-15))); // ROTL32(d, 15);
  d = caml_mul(d, 0x1b873593);
  h ^= d;
  h = ((h << 13) | (h >>> (32-13)));   //ROTL32(h, 13);
  return (((h + (h << 2))|0) + (0xe6546b64|0))|0;
}

//Provides: caml_hash_mix_final
//Requires: caml_mul
function caml_hash_mix_final(h) {
  h ^= h >>> 16;
  h = caml_mul (h, 0x85ebca6b|0);
  h ^= h >>> 13;
  h = caml_mul (h, 0xc2b2ae35|0);
  h ^= h >>> 16;
  return h;
}

//Provides: caml_hash_mix_float
//Requires: caml_hash_mix_int, caml_int64_bits_of_float
function caml_hash_mix_float (h, v0) {
  var v = caml_int64_bits_of_float (v0);
  var lo = v[1] | (v[2] << 24);
  var hi = (v[2] >>> 8) | (v[3] << 16);
  h = caml_hash_mix_int(h, lo);
  h = caml_hash_mix_int(h, hi);
  return h;
}
//Provides: caml_hash_mix_int64
//Requires: caml_hash_mix_int
function caml_hash_mix_int64 (h, v) {
  var lo = v[1] | (v[2] << 24);
  var hi = (v[2] >>> 8) | (v[3] << 16);
  h = caml_hash_mix_int(h, hi ^ lo);
  return h;
}

//Provides: caml_hash_mix_string_str
//Requires: caml_hash_mix_int
function caml_hash_mix_string_str(h, s) {
  var len = s.length, i, w;
  for (i = 0; i + 4 <= len; i += 4) {
    w = s.charCodeAt(i)
        | (s.charCodeAt(i+1) << 8)
        | (s.charCodeAt(i+2) << 16)
        | (s.charCodeAt(i+3) << 24);
    h = caml_hash_mix_int(h, w);
  }
  w = 0;
  switch (len & 3) {
  case 3: w  = s.charCodeAt(i+2) << 16;
  case 2: w |= s.charCodeAt(i+1) << 8;
  case 1: w |= s.charCodeAt(i);
          h = caml_hash_mix_int(h, w);
  default:
  }
  h ^= len;
  return h;
}

//Provides: caml_hash_mix_string_arr
//Requires: caml_hash_mix_int
function caml_hash_mix_string_arr(h, s) {
  var len = s.length, i, w;
  for (i = 0; i + 4 <= len; i += 4) {
    w = s[i]
      | (s[i+1] << 8)
      | (s[i+2] << 16)
      | (s[i+3] << 24);
    h = caml_hash_mix_int(h, w);
  }
  w = 0;
  switch (len & 3) {
  case 3: w  = s[i+2] << 16;
  case 2: w |= s[i+1] << 8;
  case 1: w |= s[i];
    h = caml_hash_mix_int(h, w);
  default:
  }
  h ^= len;
  return h;
}

//Provides: caml_hash_mix_string
//Requires: caml_convert_string_to_bytes
//Requires: caml_hash_mix_string_str
//Requires: caml_hash_mix_string_arr
function caml_hash_mix_string(h, v) {
    switch (v.t & 6) {
    default:
        caml_convert_string_to_bytes (v);
    case 0: /* BYTES */
        h = caml_hash_mix_string_str(h, v.c);
        break;
    case 2: /* ARRAY */
        h = caml_hash_mix_string_arr(h, v.c);
    }
    return h
}


//Provides: caml_hash mutable
//Requires: MlBytes
//Requires: caml_int64_bits_of_float, caml_hash_mix_int, caml_hash_mix_final
//Requires: caml_hash_mix_int64, caml_hash_mix_float, caml_hash_mix_string
var HASH_QUEUE_SIZE = 256;
function caml_hash (count, limit, seed, obj) {
    var queue, rd, wr, sz, num, h, v, i, len;
    sz = limit;
    if (sz < 0 || sz > HASH_QUEUE_SIZE) sz = HASH_QUEUE_SIZE;
    num = count;
    h = seed;
    queue = [obj]; rd = 0; wr = 1;
    while (rd < wr && num > 0) {
        v = queue[rd++];
        if (v instanceof Array && v[0] === (v[0]|0)) {
            switch (v[0]) {
            case 248:
                // Object
                h = caml_hash_mix_int(h, v[2]);
                num--;
                break;
            case 250:
                // Forward
                queue[--rd] = v[1];
                break;
            case 255:
                // Int64
                h = caml_hash_mix_int64 (h, v);
                num --;
                break;
            default:
                var tag = ((v.length - 1) << 10) | v[0];
                h = caml_hash_mix_int(h, tag);
                for (i = 1, len = v.length; i < len; i++) {
                    if (wr >= sz) break;
                    queue[wr++] = v[i];
                }
                break;
            }
        } else if (v instanceof MlBytes) {
            h = caml_hash_mix_string(h,v)
            num--;
        } else if (v === (v|0)) {
            // Integer
            h = caml_hash_mix_int(h, v+v+1);
            num--;
        } else if (v === +v) {
            // Float
            h = caml_hash_mix_float(h,v);
            num--;
        } else if(v && v.hash && typeof v.hash === "function") {
	    // Custom
	    h = caml_hash_mix_int(h, v.hash());
	}
    }
    h = caml_hash_mix_final(h);
    return h & 0x3FFFFFFF;
}

///////////// Sys
//Provides: caml_sys_time mutable
var caml_initial_time = new Date() * 0.001;
function caml_sys_time () { return new Date() * 0.001 - caml_initial_time; }
//Provides: caml_sys_get_config const
//Requires: caml_new_string
function caml_sys_get_config () {
  return [0, caml_new_string("Unix"), 32, 0];
}

//Provides: caml_sys_const_backend_type const
//Requires: caml_new_string
function caml_sys_const_backend_type () {
  return [0, caml_new_string("js_of_ocaml")];
}


//Provides: caml_sys_random_seed mutable
//Version: < 4.00
//The function needs to return an array since OCaml 4.0...
function caml_sys_random_seed () {
  var x = new Date()^0xffffffff*Math.random();
  return x;
}

//Provides: caml_sys_random_seed mutable
//Version: >= 4.00
//The function needs to return an array since OCaml 4.0...
function caml_sys_random_seed () {
  var x = new Date()^0xffffffff*Math.random();
  return [0,x];
}



//Provides: caml_sys_const_big_endian const
function caml_sys_const_big_endian () { return 0; }
//Provides: caml_sys_const_word_size const
function caml_sys_const_word_size () { return 32; }
//Provides: caml_sys_const_int_size const
function caml_sys_const_int_size () { return 32; }

//Provides: caml_sys_const_max_wosize const
// max_int / 4 so that the following does not overflow
//let max_string_length = word_size / 8 * max_array_length - 1;;
function caml_sys_const_max_wosize () { return (0x7FFFFFFF/4) | 0;}

//Provides: caml_sys_const_ostype_cygwin const
function caml_sys_const_ostype_cygwin () { return 0; }
//Provides: caml_sys_const_ostype_unix const
function caml_sys_const_ostype_unix () { return 1; }
//Provides: caml_sys_const_ostype_win32 const
function caml_sys_const_ostype_win32 () { return 0; }

//Provides: caml_sys_system_command
function caml_sys_system_command(cmd){
  var cmd = cmd.toString();
  joo_global_object.console.log(cmd);
  if (typeof require != "undefined"
      && require('child_process')
      && require('child_process').execSync) {
    try {require('child_process').execSync(cmd); return 0}
    catch (e) {return 1}
  }
  else return 127;
}

///////////// Array
//Provides: caml_array_sub mutable
function caml_array_sub (a, i, len) {
  var a2 = new Array(len+1);
  a2[0]=0;
  for(var i2 = 1, i1= i+1; i2 <= len; i2++,i1++ ){
    a2[i2]=a[i1];
  }
  return a2;
}

//Provides: caml_array_append mutable
function caml_array_append(a1, a2) {
  var l1 = a1.length, l2 = a2.length;
  var l = l1+l2-1
  var a = new Array(l);
  a[0] = 0;
  var i = 1,j = 1;
  for(;i<l1;i++) a[i]=a1[i];
  for(;i<l;i++,j++) a[i]=a2[j];
  return a;
}

//Provides: caml_array_concat mutable
function caml_array_concat(l) {
  var a = [0];
  while (l !== 0) {
    var b = l[1];
    for (var i = 1; i < b.length; i++) a.push(b[i]);
    l = l[2];
  }
  return a;
}

//Provides: caml_array_blit
function caml_array_blit(a1, i1, a2, i2, len) {
  if (i2 <= i1) {
    for (var j = 1; j <= len; j++) a2[i2 + j] = a1[i1 + j];
  } else {
    for (var j = len; j >= 1; j--) a2[i2 + j] = a1[i1 + j];
  };
  return 0;
}

///////////// CamlinternalOO
//Provides: caml_get_public_method const
var caml_method_cache = [];
function caml_get_public_method (obj, tag, cacheid) {
  var meths = obj[1];
  var ofs = caml_method_cache[cacheid];
  if (ofs === null) {
    // Make sure the array is not sparse
    for (var i = caml_method_cache.length; i < cacheid; i++)
      caml_method_cache[i] = 0;
  } else if (meths[ofs] === tag) {
    return meths[ofs - 1];
  }
  var li = 3, hi = meths[1] * 2 + 1, mi;
  while (li < hi) {
    mi = ((li+hi) >> 1) | 1;
    if (tag < meths[mi+1]) hi = mi-2;
    else li = mi;
  }
  caml_method_cache[cacheid] = li + 1;
  /* return 0 if tag is not there */
  return (tag == meths[li+1] ? meths[li] : 0);
}

//Provides: caml_final_register const
function caml_final_register () { return 0; }
//Provides: caml_final_register_called_without_value const
function caml_final_register_called_without_value () { return 0; }
//Provides: caml_final_release const
function caml_final_release () { return 0; }
//Provides: caml_backtrace_status const
function caml_backtrace_status () { return 0; }
//Provides: caml_get_exception_backtrace const
function caml_get_exception_backtrace () { return 0; }
//Provides: caml_get_exception_raw_backtrace const
function caml_get_exception_raw_backtrace () { return [0]; }
//Provides: caml_record_backtrace
function caml_record_backtrace () { return 0; }
//Provides: caml_convert_raw_backtrace const
function caml_convert_raw_backtrace () { return [0]; }
//Provides: caml_raw_backtrace_length
function caml_raw_backtrace_length() { return 0; }
//Provides: caml_raw_backtrace_next_slot
function caml_raw_backtrace_next_slot() { return 0 }
//Provides: caml_raw_backtrace_slot
//Requires: caml_invalid_argument
function caml_raw_backtrace_slot () {
  caml_invalid_argument("Printexc.get_raw_backtrace_slot: index out of bounds");
}
//Provides: caml_get_current_callstack const
function caml_get_current_callstack () { return [0]; }
//Provides: caml_sys_getenv (const)
//Requires: caml_raise_not_found
//Requires: caml_js_to_string
function caml_sys_getenv (name) {
  var g = joo_global_object;
  var n = name.toString();
  //nodejs env
  if(g.process
     && g.process.env
     && g.process.env[n] != undefined)
    return caml_js_to_string(g.process.env[n]);
  caml_raise_not_found ();
}
//Provides: caml_sys_exit
//Requires: caml_invalid_argument
function caml_sys_exit (code) {
  var g = joo_global_object;
  if(g.quit) g.quit(code);
  //nodejs
  if(g.process && g.process.exit)
    g.process.exit(code);
  caml_invalid_argument("Function 'exit' not implemented");
}

//Provides: caml_sys_get_argv const
//Requires: caml_js_to_string
//Requires: raw_array_sub
function caml_sys_get_argv () {
  var g = joo_global_object;
  var main = "a.out";
  var args = []

  if(g.process
     && g.process.argv
     && g.process.argv.length > 1) {
    var argv = g.process.argv
    //nodejs
    main = argv[1];
    args = raw_array_sub(argv,2,argv.length - 2);
  }

  var p = caml_js_to_string(main);
  var args2 = [0, p];
  for(var i = 0; i < args.length; i++)
    args2.push(caml_js_to_string(args[i]));
  return [0, p, args2];
}

//Provides: unix_inet_addr_of_string
function unix_inet_addr_of_string () {return 0;}

//Provides: caml_oo_last_id
var caml_oo_last_id = 0;

//Provides: caml_set_oo_id
//Requires: caml_oo_last_id
function caml_set_oo_id (b) {
  b[2]=caml_oo_last_id++;
  return b;
}

//Provides: caml_fresh_oo_id
//Requires: caml_oo_last_id
function caml_fresh_oo_id() {
  return caml_oo_last_id++;
}

//Provides: caml_install_signal_handler const
function caml_install_signal_handler(){return 0}


//Provides: caml_convert_raw_backtrace_slot
//Requires: caml_failwith
function caml_convert_raw_backtrace_slot(){
  caml_failwith("caml_convert_raw_backtrace_slot");
}

//Provides: caml_bswap16
function caml_bswap16(x) {
  return ((((x & 0x00FF) << 8) |
           ((x & 0xFF00) >> 8)));
}
//Provides: caml_int32_bswap
function caml_int32_bswap(x) {
  return (((x & 0x000000FF) << 24) |
          ((x & 0x0000FF00) << 8) |
          ((x & 0x00FF0000) >>> 8) |
          ((x & 0xFF000000) >>> 24));
}
//Provides: caml_int64_bswap
function caml_int64_bswap(x) {
  return [
    255,
    (((x[3] & 0x0000ff00) >> 8) |
     ((x[3] & 0x000000ff) << 8) |
     ((x[2] & 0x00ff0000))),
    (((x[2] & 0x0000ff00) >> 8) |
     ((x[2] & 0x000000ff) << 8) |
     ((x[1] & 0x00ff0000))),
    (((x[1] & 0x0000ff00) >> 8) |
     ((x[1] & 0x000000ff) << 8))]
}

//Provides: caml_list_of_js_array const (const)
function caml_list_of_js_array(a){
  var l = 0;
  for(var i=a.length - 1; i>=0; i--){
    var e = a[i];
    l = [0,e,l];
  }
  return l
}

//Provides: caml_runtime_warnings
var caml_runtime_warnings = 0;

//Provides: caml_ml_enable_runtime_warnings
//Requires: caml_runtime_warnings
function caml_ml_enable_runtime_warnings (bool) {
  caml_runtime_warnings = bool;
  return 0;
}

//Provides: caml_ml_runtime_warnings_enabled
//Requires: caml_runtime_warnings
function caml_ml_runtime_warnings_enabled (_unit) {
  return caml_runtime_warnings;
}

//Provides: caml_runtime_variant
//Requires: caml_new_string
function caml_runtime_variant(_unit) {
  return caml_new_string("");
}
//Provides: caml_runtime_parameters
//Requires: caml_new_string
function caml_runtime_parameters(_unit) {
  return caml_new_string("");
}


//Provides: caml_sys_isatty
function caml_sys_isatty(_chan) {
  return 0;
}

//Provides: caml_spacetime_enabled const (const)
function caml_spacetime_enabled(_unit) {
  return 0;
}

//Provides: caml_register_channel_for_spacetime const (const)
function caml_register_channel_for_spacetime(_channel) {
  return 0;
}

//Provides: caml_spacetime_only_works_for_native_code
//Requires: caml_failwith
function caml_spacetime_only_works_for_native_code() {
  caml_failwith("Spacetime profiling only works for native code");
}


//Provides: caml_is_js
function caml_is_js() {
  return 1;
}

//# 1 "io.js"
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2014 Jérôme Vouillon, Hugo Heuzard
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

///////////// Io

//Provides: caml_sys_close
//Requires: caml_global_data
function caml_sys_close(fd) {
  delete caml_global_data.fds[fd];
  return 0;
}

//Provides: caml_std_output
//Requires: caml_new_string, caml_ml_string_length, caml_ml_channels
function caml_std_output(chanid,s){
  var chan = caml_ml_channels[chanid];
  var str = caml_new_string(s);
  var slen = caml_ml_string_length(str);
  chan.file.write(chan.offset, str, 0, slen);
  chan.offset += slen;
  return 0;
}

//Provides: caml_sys_open
//Requires: caml_raise_sys_error, caml_global_data
//Requires: caml_create_bytes,MlFakeFile
//Requires: js_print_stderr, js_print_stdout
//Requires: caml_std_output
//Requires: resolve_fs_device
function caml_sys_open_internal(idx,output,file,flags) {
  if(caml_global_data.fds === undefined) caml_global_data.fds = new Array();
  flags=flags?flags:{};
  var info = {};
  info.file = file;
  info.offset = flags.append?file.length():0;
  info.flags = flags;
  info.output = output;
  caml_global_data.fds[idx] = info;
  if(!caml_global_data.fd_last_idx || idx > caml_global_data.fd_last_idx)
    caml_global_data.fd_last_idx = idx;
  return idx;
}
function caml_sys_open (name, flags, _perms) {
  var f = {};
  while(flags){
    switch(flags[1]){
    case 0: f.rdonly = 1;break;
    case 1: f.wronly = 1;break;
    case 2: f.append = 1;break;
    case 3: f.create = 1;break;
    case 4: f.truncate = 1;break;
    case 5: f.excl = 1; break;
    case 6: f.binary = 1;break;
    case 7: f.text = 1;break;
    case 8: f.nonblock = 1;break;
    }
    flags=flags[2];
  }
  if(f.rdonly && f.wronly)
    caml_raise_sys_error(name.toString() + " : flags Open_rdonly and Open_wronly are not compatible");
  if(f.text && f.binary)
    caml_raise_sys_error(name.toString() + " : flags Open_text and Open_binary are not compatible");
  var root = resolve_fs_device(name);
  var file = root.device.open(root.rest,f);
  var idx = caml_global_data.fd_last_idx?caml_global_data.fd_last_idx:0;
  return caml_sys_open_internal (idx+1,caml_std_output,file,f);
}
caml_sys_open_internal(0,caml_std_output, new MlFakeFile(caml_create_bytes(0))); //stdin
caml_sys_open_internal(1,js_print_stdout, new MlFakeFile(caml_create_bytes(0))); //stdout
caml_sys_open_internal(2,js_print_stderr, new MlFakeFile(caml_create_bytes(0))); //stderr


// ocaml Channels

//Provides: caml_ml_set_channel_name
function caml_ml_set_channel_name() {
  return 0
}

//Provides: caml_ml_channels
var caml_ml_channels = new Array();

//Provides: caml_ml_out_channels_list
//Requires: caml_ml_channels
function caml_ml_out_channels_list () {
  var l = 0;
  for(var c = 0; c < caml_ml_channels.length; c++){
    if(caml_ml_channels[c] && caml_ml_channels[c].opened && caml_ml_channels[c].out)
      l=[0,caml_ml_channels[c].fd,l];
  }
  return l;
}


//Provides: caml_ml_open_descriptor_out
//Requires: caml_ml_channels, caml_global_data
//Requires: caml_raise_sys_error
function caml_ml_open_descriptor_out (fd) {
  var data = caml_global_data.fds[fd];
  if(data.flags.rdonly) caml_raise_sys_error("fd "+ fd + " is readonly");
  var channel = {
    file:data.file,
    offset:data.offset,
    fd:fd,
    opened:true,
    out:true,
    buffer:""
  };
  caml_ml_channels[channel.fd]=channel;
  return channel.fd;
}

//Provides: caml_ml_open_descriptor_in
//Requires: caml_global_data,caml_sys_open,caml_raise_sys_error, caml_ml_channels
function caml_ml_open_descriptor_in (fd)  {
  var data = caml_global_data.fds[fd];
  if(data.flags.wronly) caml_raise_sys_error("fd "+ fd + " is writeonly");

  var channel = {
    file:data.file,
    offset:data.offset,
    fd:fd,
    opened:true,
    out: false,
    refill:null
  };
  caml_ml_channels[channel.fd]=channel;
  return channel.fd;
}


//Provides: caml_ml_set_binary_mode
//Requires: caml_global_data, caml_ml_channels
function caml_ml_set_binary_mode(chanid,mode){
  var chan = caml_ml_channels[chanid];
  var data = caml_global_data.fds[chan.fd];
  data.flags.text = !mode
  data.flags.binary = mode
  return 0;
}

//Input from in_channel

//Provides: caml_ml_close_channel
//Requires: caml_ml_flush, caml_ml_channels
//Requires: caml_sys_close
function caml_ml_close_channel (chanid) {
  var chan = caml_ml_channels[chanid];
  caml_ml_flush(chanid);
  chan.opened = false;
  chan.file.close();
  caml_sys_close(chan.fd)
  return 0;
}

//Provides: caml_ml_channel_size
//Requires: caml_ml_channels
function caml_ml_channel_size(chanid) {
  var chan = caml_ml_channels[chanid];
  return chan.file.length();
}

//Provides: caml_ml_channel_size_64
//Requires: caml_int64_of_float,caml_ml_channels
function caml_ml_channel_size_64(chanid) {
  var chan = caml_ml_channels[chanid];
  return caml_int64_of_float(chan.file.length ());
}

//Provides: caml_ml_set_channel_output
//Requires: caml_ml_channels, caml_global_data
function caml_ml_set_channel_output(chanid,f) {
  var chan = caml_ml_channels[chanid];
  caml_global_data.fds[chan.fd].output = f;
  return 0;
}

//Provides: caml_ml_set_channel_refill
//Requires: caml_ml_channels, caml_global_data
function caml_ml_set_channel_refill(chanid,f) {
  caml_ml_channels[chanid].refill = f;
  return 0;
}

//Provides: caml_ml_refill_input
//Requires: caml_ml_bytes_length
function caml_ml_refill_input (chan) {
  var str = chan.refill();
  var str_len = caml_ml_bytes_length(str);
  if (str_len == 0) chan.refill = null;
  chan.file.write(chan.file.length(), str, 0, str_len);
  return str_len;
}

//Provides: caml_ml_may_refill_input
//Requires: caml_ml_refill_input, caml_ml_channels
function caml_ml_may_refill_input (chanid) {
  var chan = caml_ml_channels[chanid];
  if (chan.refill == null) return;
  if (chan.file.length() != chan.offset) return;
  caml_ml_refill_input (chan);
}

//Provides: caml_ml_input
//Requires: caml_ml_refill_input, caml_ml_channels
function caml_ml_input (chanid, s, i, l) {
  var chan = caml_ml_channels[chanid];
  var l2 = chan.file.length() - chan.offset;
  if (l2 == 0 && chan.refill != null) l2 = caml_ml_refill_input(chan);
  if (l2 < l) l = l2;
  chan.file.read(chan.offset, s, i, l);
  chan.offset += l;
  return l;
}

//Provides: caml_input_value
//Requires: caml_marshal_data_size, caml_input_value_from_string, caml_create_bytes, caml_ml_channels
function caml_input_value (chanid) {
  var chan = caml_ml_channels[chanid];

  var buf = caml_create_bytes(8);
  chan.file.read(chan.offset,buf,0,8);

  // Header is 20 bytes
  var len = caml_marshal_data_size (buf, 0) + 20;

  var buf = caml_create_bytes(len);
  chan.file.read(chan.offset,buf,0,len);

  var offset = [0];
  var res = caml_input_value_from_string(buf, offset);
  chan.offset = chan.offset + offset[0];
  return res;
}

//Provides: caml_ml_input_char
//Requires: caml_raise_end_of_file, caml_array_bound_error
//Requires: caml_ml_may_refill_input, caml_ml_channels
function caml_ml_input_char (chanid) {
  var chan = caml_ml_channels[chanid];
  caml_ml_may_refill_input(chanid);
  if (chan.offset >= chan.file.length())
    caml_raise_end_of_file();
  var res = chan.file.read_one(chan.offset);
  chan.offset++;
  return res;
}

//Provides: caml_ml_input_int
//Requires: caml_raise_end_of_file
//Requires: caml_ml_refill_input, caml_ml_channels
function caml_ml_input_int (chanid) {
  var chan = caml_ml_channels[chanid];
  var file = chan.file;
  while ((chan.offset + 3) >= file.length()) {
    var l = caml_ml_refill_input(chan);
    if (l == 0) caml_raise_end_of_file();
  }
  var o = chan.offset;
  var r =(file.read_one(o  ) << 24)
      |  (file.read_one(o+1) << 16)
      |  (file.read_one(o+2) << 8)
      |  (file.read_one(o+3));
  chan.offset+=4;
  return r;
}

//Provides: caml_ml_seek_in
//Requires: caml_raise_sys_error, caml_ml_channels
function caml_ml_seek_in(chanid,pos){
  var chan = caml_ml_channels[chanid];
  if (chan.refill != null) caml_raise_sys_error("Illegal seek");
  chan.offset = pos;
  return 0;
}

//Provides: caml_ml_seek_in_64
//Requires: caml_int64_to_float, caml_raise_sys_error, caml_ml_channels
function caml_ml_seek_in_64(chanid,pos){
  var chan = caml_ml_channels[chanid];
  if (chan.refill != null) caml_raise_sys_error("Illegal seek");
  chan.offset = caml_int64_to_float(pos);
  return 0;
}

//Provides: caml_ml_pos_in
//Requires: caml_ml_channels
function caml_ml_pos_in(chanid) {return caml_ml_channels[chanid].offset}

//Provides: caml_ml_pos_in_64
//Requires: caml_int64_of_float, caml_ml_channels
function caml_ml_pos_in_64(chanid) {return caml_int64_of_float(caml_ml_channels[chanid].offset)}

//Provides: caml_ml_input_scan_line
//Requires: caml_array_bound_error
//Requires: caml_ml_may_refill_input, caml_ml_channels
function caml_ml_input_scan_line(chanid){
  var chan = caml_ml_channels[chanid];
  caml_ml_may_refill_input(chanid);
  var p = chan.offset;
  var len = chan.file.length();
  if(p >= len) { return 0;}
  while(true) {
    if(p >= len) return - (p - chan.offset);
    if(chan.file.read_one(p) == 10) return p - chan.offset + 1;
    p++;
  }
}

//Provides: caml_ml_flush
//Requires: caml_raise_sys_error, caml_global_data, caml_ml_channels
function caml_ml_flush (chanid) {
    var chan = caml_ml_channels[chanid];
    if(! chan.opened) caml_raise_sys_error("Cannot flush a closed channel");
    if(!chan.buffer || chan.buffer == "") return 0;
    if(chan.fd
       && caml_global_data.fds[chan.fd]
       && caml_global_data.fds[chan.fd].output) {
      var output = caml_global_data.fds[chan.fd].output;
      switch(output.length){
      case 2: output(chanid,chan.buffer);break;
      default: output(chan.buffer)
      };
    }
    chan.buffer = "";
    return 0;
}

//output to out_channel

//Provides: caml_ml_output_bytes
//Requires: caml_ml_flush,caml_ml_bytes_length
//Requires: caml_create_bytes, caml_blit_bytes, caml_raise_sys_error, caml_ml_channels, caml_jsbytes_of_string
function caml_ml_output_bytes(chanid,buffer,offset,len) {
    var chan = caml_ml_channels[chanid];
    if(! chan.opened) caml_raise_sys_error("Cannot output to a closed channel");
    var string;
    if(offset == 0 && caml_ml_bytes_length(buffer) == len)
        string = buffer;
    else {
        string = caml_create_bytes(len);
        caml_blit_bytes(buffer,offset,string,0,len);
    }
    var jsstring = caml_jsbytes_of_string(string);
    var id = jsstring.lastIndexOf("\n");
    if(id < 0)
        chan.buffer+=jsstring;
    else {
        chan.buffer+=jsstring.substr(0,id+1);
        caml_ml_flush (chanid);
        chan.buffer += jsstring.substr(id+1);
    }
    return 0;
}

//Provides: caml_ml_output
//Requires: caml_ml_output_bytes
function caml_ml_output(chanid,buffer,offset,len){
    return caml_ml_output_bytes(chanid,buffer,offset,len);
}

//Provides: caml_ml_output_char
//Requires: caml_ml_output
//Requires: caml_new_string
function caml_ml_output_char (chanid,c) {
    var s = caml_new_string(String.fromCharCode(c));
    caml_ml_output(chanid,s,0,1);
    return 0;
}

//Provides: caml_output_value
//Requires: caml_output_value_to_string, caml_ml_output,caml_ml_string_length
function caml_output_value (chanid,v,_flags) {
  var s = caml_output_value_to_string(v);
  caml_ml_output(chanid,s,0,caml_ml_string_length(s));
  return 0;
}


//Provides: caml_ml_seek_out
//Requires: caml_ml_channels
function caml_ml_seek_out(chanid,pos){
  caml_ml_channels[chanid].offset = pos;
  return 0;
}

//Provides: caml_ml_seek_out_64
//Requires: caml_int64_to_float, caml_ml_channels
function caml_ml_seek_out_64(chanid,pos){
  caml_ml_channels[chanid].offset = caml_int64_to_float(pos);
  return 0;
}

//Provides: caml_ml_pos_out
//Requires: caml_ml_channels
function caml_ml_pos_out(chanid) {return caml_ml_channels[chanid].offset}

//Provides: caml_ml_pos_out_64
//Requires: caml_int64_of_float, caml_ml_channels
function caml_ml_pos_out_64(chanid) {
  return caml_int64_of_float (caml_ml_channels[chanid].offset);
}

//Provides: caml_ml_output_int
//Requires: caml_ml_output
//Requires: caml_string_of_array
function caml_ml_output_int (chanid,i) {
  var arr = [(i>>24) & 0xFF,(i>>16) & 0xFF,(i>>8) & 0xFF,i & 0xFF ];
  var s = caml_string_of_array(arr);
  caml_ml_output(chanid,s,0,4);
  return 0
}

//# 1 "fs.js"
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2014 Jérôme Vouillon, Hugo Heuzard
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

///////////// Dummy filesystem

//Provides: caml_current_dir
if(joo_global_object.process && joo_global_object.process.cwd)
  var caml_current_dir = joo_global_object.process.cwd().replace(/\\/g,'/');
else
  var caml_current_dir =  "/static";
if(caml_current_dir.slice(-1) !== "/") caml_current_dir += "/"

//Provides: caml_root
//Requires: caml_current_dir
var caml_root = caml_current_dir.match(/[^\/]*\//)[0];


//Provides: MlFile
function MlFile(){  }

//Provides: caml_make_path
//Requires: caml_current_dir,MlBytes
function caml_make_path (name) {
  name=(name instanceof MlBytes)?name.toString():name;
  if(name.charCodeAt(0) != 47)
    name = caml_current_dir + name;
  var comp = name.split("/");
  var ncomp = []
  for(var i = 0; i<comp.length; i++){
    switch(comp[i]){
    case "..": if(ncomp.length>1) ncomp.pop(); break;
    case ".": break;
    case "": if(ncomp.length == 0) ncomp.push(""); break;
    default: ncomp.push(comp[i]);break
    }
  }
  ncomp.orig = name;
  return ncomp;
}

//Provides:jsoo_mount_point
//Requires: MlFakeDevice, MlNodeDevice, caml_root, fs_node_supported
var jsoo_mount_point = []
if (fs_node_supported()) {
    jsoo_mount_point.push({path:caml_root,device:new MlNodeDevice(caml_root)});
} else {
    jsoo_mount_point.push({path:caml_root,device:new MlFakeDevice(caml_root)});
}
jsoo_mount_point.push({path:caml_root+"static/", device:new MlFakeDevice(caml_root+"static/")});

//Provides:caml_list_mount_point
//Requires: jsoo_mount_point, caml_new_string
function caml_list_mount_point(){
    var prev = 0
    for(var i = 0; i < jsoo_mount_point.length; i++){
        var old = prev;
        prev = [0, caml_new_string(jsoo_mount_point[i].path), old]
    }
    return prev;
}

//Provides: resolve_fs_device
//Requires: caml_make_path, jsoo_mount_point
function resolve_fs_device(name){
  var path = caml_make_path(name);
  var name = path.join("/");
  var name_slash = name + "/";
  var res;
  for(var i = 0; i < jsoo_mount_point.length; i++) {
    var m = jsoo_mount_point[i];
    if(name_slash.search(m.path) == 0
       && (!res || res.path.length < m.path.length))
        res = {path:m.path,device:m.device,rest:name.substring(m.path.length,name.length)};
  }
  return res;
}

//Provides: caml_mount_autoload
//Requires: MlFakeDevice, caml_make_path, jsoo_mount_point
function caml_mount_autoload(name,f){
  var path = caml_make_path(name);
  var name = path.join("/") + "/";
  jsoo_mount_point.push({path:name,device:new MlFakeDevice(name,f)})
  return 0;
}

//Provides: caml_unmount
//Requires: jsoo_mount_point, caml_make_path
function caml_unmount(name){
  var path = caml_make_path(name);
  var name = path.join("/") + "/";
  var idx = -1;
  for(var i = 0; i < jsoo_mount_point.length; i++)
    if(jsoo_mount_point[i].path == name) idx = i;
  if(idx > -1) jsoo_mount_point.splice(idx,1);
  return 0
}

//Provides: caml_sys_getcwd
//Requires: caml_current_dir, caml_new_string
function caml_sys_getcwd() {
  return caml_new_string(caml_current_dir);
}

//Provides: caml_sys_chdir
//Requires: caml_current_dir, caml_raise_no_such_file, resolve_fs_device
function caml_sys_chdir(dir) {
  var root = resolve_fs_device(dir);
  if(root.device.exists(root.rest)) {
    if(root.rest) caml_current_dir = root.path + root.rest + "/";
    else caml_current_dir = root.path;
    return 0;
  }
  else {
    caml_raise_no_such_file(dir);
  }
}

//Provides: caml_raise_no_such_file
//Requires: MlBytes, caml_raise_sys_error
function caml_raise_no_such_file(name){
  name = (name instanceof MlBytes)?name.toString():name;
  caml_raise_sys_error (name + ": No such file or directory");
}

//Provides: caml_raise_not_a_dir
//Requires: MlBytes, caml_raise_sys_error
function caml_raise_not_a_dir(name){
  name = (name instanceof MlBytes)?name.toString():name;
  caml_raise_sys_error (name + ": Not a directory");
}

//Provides: caml_sys_file_exists
//Requires: resolve_fs_device
function caml_sys_file_exists (name) {
  var root = resolve_fs_device(name);
  return root.device.exists(root.rest);
}

//Provides: caml_sys_read_directory
//Requires: caml_new_string
//Requires: caml_raise_not_a_dir, resolve_fs_device
function caml_sys_read_directory(name){
  var root = resolve_fs_device(name);
  var a = root.device.readdir(root.rest);
  var l = new Array(a.length + 1);
  l[0] = 0;
  for(var i=0;i<a.length;i++)
    l[i+1] = caml_new_string(a[i]);
  return l;
}

//Provides: caml_sys_remove
//Requires: caml_raise_no_such_file, resolve_fs_device
function caml_sys_remove(name){
  var root = resolve_fs_device(name);
  var ok = root.device.unlink(root.rest);
  if(ok == 0) caml_raise_no_such_file(name);
  return 0;
}

//Provides: caml_sys_is_directory
//Requires: resolve_fs_device
function caml_sys_is_directory(name){
  var root = resolve_fs_device(name);
  var a = root.device.is_dir(root.rest);
  return a?1:0;
}

//Provides: caml_sys_rename
//Requires: caml_failwith, resolve_fs_device
function caml_sys_rename(o,n){
  var o_root = resolve_fs_device(o);
  var n_root = resolve_fs_device(n);
  if(o_root.device != n_root.device)
    caml_failwith("caml_sys_rename: cannot move file between two filesystem");
  if(!o_root.device.rename)
    caml_failwith("caml_sys_rename: no implemented");
  o_root.device.rename(o_root.rest, n_root.rest);
}


//Provides: caml_ba_map_file
//Requires: caml_failwith
function caml_ba_map_file(vfd, kind, layout, shared, dims, pos) {
  // var data = caml_global_data.fds[vfd];
  caml_failwith("caml_ba_map_file not implemented");
}

//Provides: caml_ba_map_file_bytecode
//Requires: caml_ba_map_file
function caml_ba_map_file_bytecode(argv,argn){
  return caml_ba_map_file(argv[0],argv[1],argv[2],argv[3],argv[4],argv[5]);
}

//Provides: caml_create_file_extern
function caml_create_file_extern(name,content){
  if(joo_global_object.caml_create_file)
    joo_global_object.caml_create_file(name,content);
  else {
    if(!joo_global_object.caml_fs_tmp) joo_global_object.caml_fs_tmp = [];
    joo_global_object.caml_fs_tmp.push({name:name,content:content});
  }
  return 0;
}

//Provides: caml_fs_init
//Requires: caml_create_file
function caml_fs_init (){
  var tmp=joo_global_object.caml_fs_tmp
  if(tmp){
    for(var i = 0; i < tmp.length; i++){
      caml_create_file(tmp[i].name,tmp[i].content);
    }
  }
  joo_global_object.caml_create_file = caml_create_file;
  return 0;
}

//Provides: caml_create_file
//Requires: caml_failwith, resolve_fs_device
function caml_create_file(name,content) {
  var root = resolve_fs_device(name);
  if(! root.device.register) caml_failwith("cannot register file");
  root.device.register(root.rest,content);
  return 0;
}

//Provides: caml_read_file_content
//Requires: resolve_fs_device, caml_raise_no_such_file, caml_create_bytes
function caml_read_file_content (name) {
  var root = resolve_fs_device(name);
  if(root.device.exists(root.rest)) {
    var file = root.device.open(root.rest,{rdonly:1});
    var len  = file.length();
    var buf  = caml_create_bytes(len);
    file.read(0,buf,0,len);
    return buf
  }
  caml_raise_no_such_file(name);
}

//# 1 "fs_fake.js"
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2014 Jérôme Vouillon, Hugo Heuzard
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

//Provides: MlFakeDevice
//Requires: MlFakeFile, caml_create_bytes
//Requires: caml_raise_sys_error, caml_raise_no_such_file, caml_new_string, caml_string_of_array
//Requires: MlBytes
function MlFakeDevice (root, f) {
  this.content={};
  this.root = root;
  this.lookupFun = f;
}
MlFakeDevice.prototype.nm = function(name) {
  return (this.root + name);
}
MlFakeDevice.prototype.lookup = function(name) {
  if(!this.content[name] && this.lookupFun) {
    var res = this.lookupFun(caml_new_string(this.root), caml_new_string(name));
    if(res != 0) this.content[name]=new MlFakeFile(res[1]);
  }
}
MlFakeDevice.prototype.exists = function(name) {
  // The root of the device exists
  if(name == "") return 1;
  // Check if a directory exists
  var name_slash = (name + "/");
  var r = new RegExp("^" + name_slash);
  for(var n in this.content) {
    if (n.match(r)) return 1
  }
  // Check if a file exists
  this.lookup(name);
  return this.content[name]?1:0;
}
MlFakeDevice.prototype.readdir = function(name) {
  var name_slash = (name == "")?"":(name + "/");
  var r = new RegExp("^" + name_slash + "([^/]*)");
  var seen = {}
  var a = [];
  for(var n in this.content) {
    var m = n.match(r);
    if(m && !seen[m[1]]) {seen[m[1]] = true; a.push(m[1])}
  }
  return a;
}
MlFakeDevice.prototype.is_dir = function(name) {
  var name_slash = (name == "")?"":(name + "/");
  var r = new RegExp("^" + name_slash + "([^/]*)");
  var a = [];
  for(var n in this.content) {
    var m = n.match(r);
    if(m) return 1
  }
  return 0
}
MlFakeDevice.prototype.unlink = function(name) {
  var ok = this.content[name]?true:false;
  delete this.content[name];
  return ok;
}
MlFakeDevice.prototype.open = function(name, f) {
  if(f.rdonly && f.wronly)
    caml_raise_sys_error(this.nm(name) + " : flags Open_rdonly and Open_wronly are not compatible");
  if(f.text && f.binary)
    caml_raise_sys_error(this.nm(name) + " : flags Open_text and Open_binary are not compatible");
  this.lookup(name);
  if (this.content[name]) {
    if (this.is_dir(name)) caml_raise_sys_error(this.nm(name) + " : is a directory");
    if (f.create && f.excl) caml_raise_sys_error(this.nm(name) + " : file already exists");
    var file = this.content[name];
    if(f.truncate) file.truncate();
    return file;
  } else if (f.create) {
    this.content[name] = new MlFakeFile(caml_create_bytes(0));
    return this.content[name];
  } else {
    caml_raise_no_such_file (this.nm(name));
  }
}

MlFakeDevice.prototype.register= function (name,content){
  if(this.content[name]) caml_raise_sys_error(this.nm(name) + " : file already exists");
  if(content instanceof MlBytes)
    this.content[name] = new MlFakeFile(content);
  else if(content instanceof Array)
    this.content[name] = new MlFakeFile(caml_string_of_array(content));
  else if(content.toString) {
    var mlstring = caml_new_string(content.toString());
    this.content[name] = new MlFakeFile(mlstring);
  }
}

MlFakeDevice.prototype.constructor = MlFakeDevice

//Provides: MlFakeFile
//Requires: MlFile
//Requires: caml_create_bytes, caml_ml_bytes_length,caml_blit_bytes
//Requires: caml_bytes_get
function MlFakeFile(content){
  this.data = content;
}
MlFakeFile.prototype = new MlFile ();
MlFakeFile.prototype.truncate = function(len){
  var old = this.data;
  this.data = caml_create_bytes(len|0);
  caml_blit_bytes(old, 0, this.data, 0, len);
}
MlFakeFile.prototype.length = function () {
  return caml_ml_bytes_length(this.data);
}
MlFakeFile.prototype.write = function(offset,buf,pos,len){
  var clen = this.length();
  if(offset + len >= clen) {
    var new_str = caml_create_bytes(offset + len);
    var old_data = this.data;
    this.data = new_str;
    caml_blit_bytes(old_data, 0, this.data, 0, clen);
  }
  caml_blit_bytes(buf, pos, this.data, offset, len);
  return 0
}
MlFakeFile.prototype.read = function(offset,buf,pos,len){
  var clen = this.length();
  caml_blit_bytes(this.data, offset, buf, pos, len);
  return 0
}
MlFakeFile.prototype.read_one = function(offset){
  return caml_bytes_get(this.data, offset);
}
MlFakeFile.prototype.close = function(){

}
MlFakeFile.prototype.constructor = MlFakeFile

//# 1 "fs_node.js"
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2014 Jérôme Vouillon, Hugo Heuzard
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

//Provides: fs_node_supported
function fs_node_supported () {
  return (
    typeof joo_global_object.process !== 'undefined'
      && typeof joo_global_object.process.versions !== 'undefined'
      && typeof joo_global_object.process.versions.node !== 'undefined')
}

//Provides: MlNodeDevice
//Requires: MlNodeFile
function MlNodeDevice(root) {
  this.fs = require('fs');
  this.root = root;
}
MlNodeDevice.prototype.nm = function(name) {
  return (this.root + name);
}
MlNodeDevice.prototype.exists = function(name) {
  return this.fs.existsSync(this.nm(name))?1:0;
}
MlNodeDevice.prototype.readdir = function(name) {
  return this.fs.readdirSync(this.nm(name));
}
MlNodeDevice.prototype.is_dir = function(name) {
  return this.fs.statSync(this.nm(name)).isDirectory()?1:0;
}
MlNodeDevice.prototype.unlink = function(name) {
  var b = this.fs.existsSync(this.nm(name))?1:0;
  this.fs.unlinkSync(this.nm(name));
  return b
}
MlNodeDevice.prototype.open = function(name, f) {
  var consts = require('constants');
  var res = 0;
  for(var key in f){
    switch(key){
    case "rdonly"  : res |= consts.O_RDONLY; break;
    case "wronly"  : res |= consts.O_WRONLY; break;
    case "append"  :
      res |= consts.O_WRONLY | consts.O_APPEND;
      break;
    case "create"   : res |= consts.O_CREAT;    break;
    case "truncate" : res |= consts.O_TRUNC;    break;
    case "excl"     : res |= consts.O_EXCL;     break;
    case "binary"   : res |= consts.O_BINARY;   break;
    case "text"     : res |= consts.O_TEXT;     break;
    case "nonblock" : res |= consts.O_NONBLOCK; break;
    }
  }
  var fd = this.fs.openSync(this.nm(name), res);
  return new MlNodeFile(fd);
}

MlNodeDevice.prototype.rename = function(o,n) {
  this.fs.renameSync(this.nm(o), this.nm(n));
}

MlNodeDevice.prototype.constructor = MlNodeDevice

//Provides: MlNodeFile
//Requires: MlFile, caml_array_of_string, caml_bytes_set

var Buffer = joo_global_object.Buffer

function MlNodeFile(fd){
  this.fs = require('fs');
  this.fd = fd;
}
MlNodeFile.prototype = new MlFile ();

MlNodeFile.prototype.truncate = function(len){
  this.fs.ftruncateSync(this.fd,len|0)
}
MlNodeFile.prototype.length = function () {
  return this.fs.fstatSync(this.fd).size;
}
MlNodeFile.prototype.write = function(offset,buf,buf_offset,len){
  var a = caml_array_of_string(buf);
  if(! (a instanceof joo_global_object.Uint8Array))
    a = new joo_global_object.Uint8Array(a);
  var buffer = new Buffer (a);
  this.fs.writeSync(this.fd, buffer, buf_offset, len, offset);
  return 0;
}
MlNodeFile.prototype.read = function(offset,buf,buf_offset,len){
  var a = caml_array_of_string(buf);
  if(! (a instanceof joo_global_object.Uint8Array))
    a = new joo_global_object.Uint8Array(a);
  var buffer = new Buffer(a);
  this.fs.readSync(this.fd, buffer, buf_offset, len, offset);
  for(var i = 0; i < len; i++){
    caml_bytes_set(buf,buf_offset + i,buffer[buf_offset+i]);
  }
  return 0
}
MlNodeFile.prototype.read_one = function(offset){
  var a = new joo_global_object.Uint8Array(1);
  var buffer = new Buffer(a);
  this.fs.readSync(this.fd, buffer, 0, 1, offset);
  return buffer[0];
}
MlNodeFile.prototype.close = function(){
  this.fs.closeSync(this.fd);
}

MlNodeFile.prototype.constructor = MlNodeFile;

//# 1 "jslib.js"
// Js_of_ocaml library
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

///////////// Jslib

//Provides: caml_js_pure_expr const
function caml_js_pure_expr (f) { return f(); }

//Provides: caml_js_set (mutable, const, const)
function caml_js_set(o,f,v) { o[f]=v;return 0}
//Provides: caml_js_get mutable (const, const)
function caml_js_get(o,f) { return o[f]; }
//Provides: caml_js_delete (mutable, const)
function caml_js_delete(o,f) { delete o[f]; return 0}

//Provides: caml_js_instanceof (const, const)
function caml_js_instanceof(o,c) { return o instanceof c; }

//Provides: caml_js_typeof (const)
function caml_js_typeof(o) { return typeof o; }

//Provides: caml_js_on_ie const
function caml_js_on_ie () {
  var ua =
    joo_global_object.navigator?joo_global_object.navigator.userAgent:"";
  return ua.indexOf("MSIE") != -1 && ua.indexOf("Opera") != 0;
}

//Provides: caml_js_html_escape const (const)
var caml_js_regexps = { amp:/&/g, lt:/</g, quot:/\"/g, all:/[&<\"]/ };
function caml_js_html_escape (s) {
  if (!caml_js_regexps.all.test(s)) return s;
  return s.replace(caml_js_regexps.amp, "&amp;")
          .replace(caml_js_regexps.lt, "&lt;")
          .replace(caml_js_regexps.quot, "&quot;");
}

//Provides: caml_js_html_entities const (const)
function caml_js_html_entities(s) {
    var str, temp = document.createElement('p');
    temp.innerHTML= s;
    str= temp.textContent || temp.innerText;
    temp=null;
    return str;
}

/////////// Debugging console
//Provides: caml_js_get_console const
function caml_js_get_console () {
  var c = joo_global_object.console?joo_global_object.console:{};
  var m = ["log", "debug", "info", "warn", "error", "assert", "dir", "dirxml",
           "trace", "group", "groupCollapsed", "groupEnd", "time", "timeEnd"];
  function f () {}
  for (var i = 0; i < m.length; i++) if (!c[m[i]]) c[m[i]]=f;
  return c;
}

//Provides:caml_trampoline
function caml_trampoline(res) {
  var c = 1;
  while(res && res.joo_tramp){
    res = res.joo_tramp.apply(null, res.joo_args);
    c++;
  }
  return res;
}

//Provides:caml_trampoline_return
function caml_trampoline_return(f,args) {
  return {joo_tramp:f,joo_args:args};
}

//Provides: js_print_stdout (const)
function js_print_stdout(s) {
  var g = joo_global_object;
  if (g.process && g.process.stdout && g.process.stdout.write) {
    g.process.stdout.write(s)
  } else {
  // Do not output the last \n if present
  // as console logging display a newline at the end
  if(s.charCodeAt(s.length - 1) == 10)
    s = s.substr(0,s.length - 1 );
  var v = g.console;
  v  && v.log && v.log(s);
  }
}
//Provides: js_print_stderr (const)
function js_print_stderr(s) {
  var g = joo_global_object;
  if (g.process && g.process.stdout && g.process.stdout.write) {
    g.process.stderr.write(s)
  } else {
  // Do not output the last \n if present
  // as console logging display a newline at the end
  if(s.charCodeAt(s.length - 1) == 10)
    s = s.substr(0,s.length - 1 );
  var v = g.console;
  v && v.error && v.error(s);
  }
}

//# 1 "jslib_js_of_ocaml.js"
// Js_of_ocaml library
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

///////////// Jslib: code specific to Js_of_ocaml

//Provides: caml_js_from_bool const (const)
function caml_js_from_bool(x) { return !!x; }
//Provides: caml_js_to_bool const (const)
function caml_js_to_bool(x) { return +x; }
//Provides: caml_js_from_float const (const)
function caml_js_from_float(x) { return x; }
//Provides: caml_js_to_float const (const)
function caml_js_to_float(x) { return x; }
//Provides: caml_js_from_string mutable (const)
//Requires: MlBytes
function caml_js_from_string(s) { return s.toString(); }
//Provides: caml_js_from_array mutable (shallow)
//Requires: raw_array_sub
function caml_js_from_array(a) { return raw_array_sub(a,1,a.length-1); }
//Provides: caml_js_to_array mutable (shallow)
//Requires: raw_array_cons
function caml_js_to_array(a) { return raw_array_cons(a,0); }

//Provides: caml_js_var mutable (const)
//Requires: js_print_stderr
//Requires: MlBytes
function caml_js_var(x) {
  var x = x.toString();
  //Checks that x has the form ident[.ident]*
  if(!x.match(/^[a-zA-Z_$][a-zA-Z_$0-9]*(\.[a-zA-Z_$][a-zA-Z_$0-9]*)*$/)){
    js_print_stderr("caml_js_var: \"" + x + "\" is not a valid JavaScript variable. continuing ..");
    //joo_global_object.console.error("Js.Unsafe.eval_string")
  }
  return eval(x);
}
//Provides: caml_js_call (const, mutable, shallow)
//Requires: caml_js_from_array
function caml_js_call(f, o, args) { return f.apply(o, caml_js_from_array(args)); }
//Provides: caml_js_fun_call (const, shallow)
//Requires: caml_js_from_array
function caml_js_fun_call(f, a) {
  switch (a.length) {
  case 1: return f();
  case 2: return f (a[1]);
  case 3: return f (a[1],a[2]);
  case 4: return f (a[1],a[2],a[3]);
  case 5: return f (a[1],a[2],a[3],a[4]);
  case 6: return f (a[1],a[2],a[3],a[4],a[5]);
  case 7: return f (a[1],a[2],a[3],a[4],a[5],a[6]);
  case 8: return f (a[1],a[2],a[3],a[4],a[5],a[6],a[7]);
  }
  return f.apply(null, caml_js_from_array(a));
}
//Provides: caml_js_meth_call (mutable, const, shallow)
//Requires: MlBytes
//Requires: caml_js_from_array
function caml_js_meth_call(o, f, args) {
  return o[f.toString()].apply(o, caml_js_from_array(args));
}
//Provides: caml_js_new (const, shallow)
//Requires: caml_js_from_array
function caml_js_new(c, a) {
  switch (a.length) {
  case 1: return new c;
  case 2: return new c (a[1]);
  case 3: return new c (a[1],a[2]);
  case 4: return new c (a[1],a[2],a[3]);
  case 5: return new c (a[1],a[2],a[3],a[4]);
  case 6: return new c (a[1],a[2],a[3],a[4],a[5]);
  case 7: return new c (a[1],a[2],a[3],a[4],a[5],a[6]);
  case 8: return new c (a[1],a[2],a[3],a[4],a[5],a[6],a[7]);
  }
  function F() { return c.apply(this, caml_js_from_array(a)); }
  F.prototype = c.prototype;
  return new F;
}
//Provides: caml_ojs_new_arr (const, shallow)
//Requires: caml_js_from_array
function caml_ojs_new_arr(c, a) {
  switch (a.length) {
  case 0: return new c;
  case 1: return new c (a[0]);
  case 2: return new c (a[0],a[1]);
  case 3: return new c (a[0],a[1],a[2]);
  case 4: return new c (a[0],a[1],a[2],a[3]);
  case 5: return new c (a[0],a[1],a[2],a[3],a[4]);
  case 6: return new c (a[0],a[1],a[2],a[3],a[4],a[5]);
  case 7: return new c (a[0],a[1],a[2],a[3],a[4],a[5],a[6]);
  }
  function F() { return c.apply(this, a); }
  F.prototype = c.prototype;
  return new F;
}
//Provides: caml_js_wrap_callback const (const)
//Requires: caml_call_gen
function caml_js_wrap_callback(f) {
  return function () {
    if(arguments.length > 0){
      return caml_call_gen(f, arguments);
    } else {
      return caml_call_gen(f, [undefined]);
    }
  }
}

//Provides: caml_js_wrap_callback_arguments
//Requires: caml_js_wrap_callback
function caml_js_wrap_callback_arguments(f) {
  return function() {
    return caml_js_wrap_callback(f)(arguments);
  }
}
//Provides: caml_js_wrap_callback_strict const
//Requires: caml_call_gen
function caml_js_wrap_callback_strict(arity, f) {
  return function () {
    var n = arguments.length;
    if(n == arity) return caml_call_gen(f, arguments);
    var args = new Array(arity);
    for (var i = 0; i < n && i < arity; i++) args[i] = arguments[i];
    return caml_call_gen(f, args);
  };
}
//Provides: caml_js_wrap_meth_callback const (const)
//Requires: caml_call_gen,raw_array_cons
function caml_js_wrap_meth_callback(f) {
  return function () {
    return caml_call_gen(f,raw_array_cons(arguments,this));
  }
}
//Provides: caml_js_wrap_meth_callback_arguments const (const)
//Requires: caml_call_gen,raw_array_cons
function caml_js_wrap_meth_callback_arguments(f) {
  return function () {
    return caml_call_gen(f,[this,arguments]);
  }
}
//Provides: caml_js_wrap_meth_callback_strict const
//Requires: caml_call_gen, raw_array_cons
function caml_js_wrap_meth_callback_strict(arity, f) {
  return function () {
    var n = arguments.length;
    if(n == arity) return caml_call_gen(f, raw_array_cons(arguments,this));
    var args = new Array(arity + 1);
    args[0] = this;
    for (var i = 1; i < n && i <= arity; i++) args[i] = arguments[i];
    return caml_call_gen(f, args);
  };
}
//Provides: caml_js_wrap_meth_callback_unsafe const (const)
//Requires: caml_call_gen,raw_array_cons
function caml_js_wrap_meth_callback_unsafe(f) {
  return function () { f.apply(null, raw_array_cons(arguments,this)); }
}
//Provides: caml_js_equals mutable (const, const)
function caml_js_equals (x, y) { return +(x == y); }
//Provides: caml_js_to_byte_string const
//Requires: caml_new_string
function caml_js_to_byte_string (s) {return caml_new_string (s);}

//Provides: caml_js_eval_string (const)
//Requires: MlBytes
function caml_js_eval_string (s) {return eval(s.toString());}

//Provides: caml_js_expr (const)
//Requires: js_print_stderr
//Requires: MlBytes
function caml_js_expr(s) {
  js_print_stderr("caml_js_expr: fallback to runtime evaluation");
  return eval(s.toString());}

//Provides: caml_pure_js_expr const (const)
//Requires: js_print_stderr
//Requires: MlBytes
function caml_pure_js_expr (s){
  js_print_stderr("caml_pure_js_expr: fallback to runtime evaluation");
  return eval(s.toString());}

//Provides: caml_js_object (object_literal)
//Requires: MlBytes
function caml_js_object (a) {
  var o = {};
  for (var i = 1; i < a.length; i++) {
    var p = a[i];
    o[p[1].toString()] = p[2];
  }
  return o;
}


//Provides: caml_js_export_var
function caml_js_export_var (){
  if(typeof module !== 'undefined' && module && module.exports)
    return module.exports
  else
    return joo_global_object;
}

//# 1 "internalMod.js"
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2014 Jérôme Vouillon, Hugo Heuzard
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

//Provides: caml_CamlinternalMod_init_mod
//Requires: caml_raise_with_arg, caml_global_data
function caml_CamlinternalMod_init_mod(loc,shape) {
  function undef_module (_x) {
    caml_raise_with_arg(caml_global_data.Undefined_recursive_module, loc);
  }
  function loop (shape,struct,idx){
    if(typeof shape === "number")
      switch(shape){
      case 0://function
        struct[idx]={fun:undef_module};
        break;
      case 1://lazy
        struct[idx]=[246, undef_module];
        break;
      default://case 2://class
        struct[idx]=[];
      }
    else
      switch(shape[0]){
      case 0://module
        struct[idx] = [0];
        for(var i=1;i<shape[1].length;i++)
          loop(shape[1][i],struct[idx],i);
        break;
      default://case 1://Value
        struct[idx] = shape[1];
      }
  }
  var res = [];
  loop(shape,res,0);
  return res[0]
}
//Provides: caml_CamlinternalMod_update_mod
//Requires: caml_update_dummy
function caml_CamlinternalMod_update_mod(shape,real,x) {
  if(typeof shape === "number")
    switch(shape){
    case 0://function
      real.fun = x;
      break;
    case 1://lazy
    default://case 2://class
      caml_update_dummy(real,x);
    }
  else
    switch(shape[0]){
    case 0://module
      for(var i=1;i<shape[1].length;i++)
        caml_CamlinternalMod_update_mod(shape[1][i],real[i],x[i]);
      break;
    //case 1://Value
    default:
    };
  return 0
}

//# 1 "gc.js"


//Provides: caml_gc_minor
function caml_gc_minor(){ return 0}
//Provides: caml_gc_major
function caml_gc_major(){ return 0}
//Provides: caml_gc_full_major
function caml_gc_full_major(){ return 0}
//Provides: caml_gc_compaction
function caml_gc_compaction(){ return 0}
//Provides: caml_gc_counters
function caml_gc_counters() { return [254,0,0,0] }
//Provides: caml_gc_quick_stat
function caml_gc_quick_stat(){
  return [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
}
//Provides: caml_gc_stat
function caml_gc_stat() {
  return [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
}

//Provides: caml_gc_set
function caml_gc_set(_control) {
  return 0;
}

//Provides: caml_gc_get
function caml_gc_get(){
  return [0,0,0,0,0,0,0,0,0]
}

//# 1 "polyfill/json2.js"
/*
    json2.js
    2015-05-03

    Public Domain.

    NO WARRANTY EXPRESSED OR IMPLIED. USE AT YOUR OWN RISK.

    See http://www.JSON.org/js.html


    This code should be minified before deployment.
    See http://javascript.crockford.com/jsmin.html

    USE YOUR OWN COPY. IT IS EXTREMELY UNWISE TO LOAD CODE FROM SERVERS YOU DO
    NOT CONTROL.


    This file creates a global JSON object containing two methods: stringify
    and parse. This file is provides the ES5 JSON capability to ES3 systems.
    If a project might run on IE8 or earlier, then this file should be included.
    This file does nothing on ES5 systems.

        JSON.stringify(value, replacer, space)
            value       any JavaScript value, usually an object or array.

            replacer    an optional parameter that determines how object
                        values are stringified for objects. It can be a
                        function or an array of strings.

            space       an optional parameter that specifies the indentation
                        of nested structures. If it is omitted, the text will
                        be packed without extra whitespace. If it is a number,
                        it will specify the number of spaces to indent at each
                        level. If it is a string (such as '\t' or '&nbsp;'),
                        it contains the characters used to indent at each level.

            This method produces a JSON text from a JavaScript value.

            When an object value is found, if the object contains a toJSON
            method, its toJSON method will be called and the result will be
            stringified. A toJSON method does not serialize: it returns the
            value represented by the name/value pair that should be serialized,
            or undefined if nothing should be serialized. The toJSON method
            will be passed the key associated with the value, and this will be
            bound to the value

            For example, this would serialize Dates as ISO strings.

                Date.prototype.toJSON = function (key) {
                    function f(n) {
                        // Format integers to have at least two digits.
                        return n < 10 
                            ? '0' + n 
                            : n;
                    }

                    return this.getUTCFullYear()   + '-' +
                         f(this.getUTCMonth() + 1) + '-' +
                         f(this.getUTCDate())      + 'T' +
                         f(this.getUTCHours())     + ':' +
                         f(this.getUTCMinutes())   + ':' +
                         f(this.getUTCSeconds())   + 'Z';
                };

            You can provide an optional replacer method. It will be passed the
            key and value of each member, with this bound to the containing
            object. The value that is returned from your method will be
            serialized. If your method returns undefined, then the member will
            be excluded from the serialization.

            If the replacer parameter is an array of strings, then it will be
            used to select the members to be serialized. It filters the results
            such that only members with keys listed in the replacer array are
            stringified.

            Values that do not have JSON representations, such as undefined or
            functions, will not be serialized. Such values in objects will be
            dropped; in arrays they will be replaced with null. You can use
            a replacer function to replace those with JSON values.
            JSON.stringify(undefined) returns undefined.

            The optional space parameter produces a stringification of the
            value that is filled with line breaks and indentation to make it
            easier to read.

            If the space parameter is a non-empty string, then that string will
            be used for indentation. If the space parameter is a number, then
            the indentation will be that many spaces.

            Example:

            text = JSON.stringify(['e', {pluribus: 'unum'}]);
            // text is '["e",{"pluribus":"unum"}]'


            text = JSON.stringify(['e', {pluribus: 'unum'}], null, '\t');
            // text is '[\n\t"e",\n\t{\n\t\t"pluribus": "unum"\n\t}\n]'

            text = JSON.stringify([new Date()], function (key, value) {
                return this[key] instanceof Date 
                    ? 'Date(' + this[key] + ')' 
                    : value;
            });
            // text is '["Date(---current time---)"]'


        JSON.parse(text, reviver)
            This method parses a JSON text to produce an object or array.
            It can throw a SyntaxError exception.

            The optional reviver parameter is a function that can filter and
            transform the results. It receives each of the keys and values,
            and its return value is used instead of the original value.
            If it returns what it received, then the structure is not modified.
            If it returns undefined then the member is deleted.

            Example:

            // Parse the text. Values that look like ISO date strings will
            // be converted to Date objects.

            myData = JSON.parse(text, function (key, value) {
                var a;
                if (typeof value === 'string') {
                    a =
/^(\d{4})-(\d{2})-(\d{2})T(\d{2}):(\d{2}):(\d{2}(?:\.\d*)?)Z$/.exec(value);
                    if (a) {
                        return new Date(Date.UTC(+a[1], +a[2] - 1, +a[3], +a[4],
                            +a[5], +a[6]));
                    }
                }
                return value;
            });

            myData = JSON.parse('["Date(09/09/2001)"]', function (key, value) {
                var d;
                if (typeof value === 'string' &&
                        value.slice(0, 5) === 'Date(' &&
                        value.slice(-1) === ')') {
                    d = new Date(value.slice(5, -1));
                    if (d) {
                        return d;
                    }
                }
                return value;
            });


    This is a reference implementation. You are free to copy, modify, or
    redistribute.
*/

/*jslint 
    eval, for, this 
*/

/*property
    JSON, apply, call, charCodeAt, getUTCDate, getUTCFullYear, getUTCHours,
    getUTCMinutes, getUTCMonth, getUTCSeconds, hasOwnProperty, join,
    lastIndex, length, parse, prototype, push, replace, slice, stringify,
    test, toJSON, toString, valueOf
*/


// Create a JSON object only if one does not already exist. We create the
// methods in a closure to avoid creating global variables.
//Provides: JSON
//Version-IE: < 8
var JSON = joo_global_object.JSON;
if (typeof JSON !== 'object') {
    JSON = {};
}

(function () {
    'use strict';
    
    var rx_one = /^[\],:{}\s]*$/,
        rx_two = /\\(?:["\\\/bfnrt]|u[0-9a-fA-F]{4})/g,
        rx_three = /"[^"\\\n\r]*"|true|false|null|-?\d+(?:\.\d*)?(?:[eE][+\-]?\d+)?/g,
        rx_four = /(?:^|:|,)(?:\s*\[)+/g,
        rx_escapable = /[\\\"\u0000-\u001f\u007f-\u009f\u00ad\u0600-\u0604\u070f\u17b4\u17b5\u200c-\u200f\u2028-\u202f\u2060-\u206f\ufeff\ufff0-\uffff]/g,
        rx_dangerous = /[\u0000\u00ad\u0600-\u0604\u070f\u17b4\u17b5\u200c-\u200f\u2028-\u202f\u2060-\u206f\ufeff\ufff0-\uffff]/g;

    function f(n) {
        // Format integers to have at least two digits.
        return n < 10 
            ? '0' + n 
            : n;
    }
    
    function this_value() {
        return this.valueOf();
    }

    if (typeof Date.prototype.toJSON !== 'function') {

        Date.prototype.toJSON = function () {

            return isFinite(this.valueOf())
                ? this.getUTCFullYear() + '-' +
                        f(this.getUTCMonth() + 1) + '-' +
                        f(this.getUTCDate()) + 'T' +
                        f(this.getUTCHours()) + ':' +
                        f(this.getUTCMinutes()) + ':' +
                        f(this.getUTCSeconds()) + 'Z'
                : null;
        };

        Boolean.prototype.toJSON = this_value;
        Number.prototype.toJSON = this_value;
        String.prototype.toJSON = this_value;
    }

    var gap,
        indent,
        meta,
        rep;


    function quote(string) {

// If the string contains no control characters, no quote characters, and no
// backslash characters, then we can safely slap some quotes around it.
// Otherwise we must also replace the offending characters with safe escape
// sequences.

        rx_escapable.lastIndex = 0;
        return rx_escapable.test(string) 
            ? '"' + string.replace(rx_escapable, function (a) {
                var c = meta[a];
                return typeof c === 'string'
                    ? c
                    : '\\u' + ('0000' + a.charCodeAt(0).toString(16)).slice(-4);
            }) + '"' 
            : '"' + string + '"';
    }


    function str(key, holder) {

// Produce a string from holder[key].

        var i,          // The loop counter.
            k,          // The member key.
            v,          // The member value.
            length,
            mind = gap,
            partial,
            value = holder[key];

// If the value has a toJSON method, call it to obtain a replacement value.

        if (value && typeof value === 'object' &&
                typeof value.toJSON === 'function') {
            value = value.toJSON(key);
        }

// If we were called with a replacer function, then call the replacer to
// obtain a replacement value.

        if (typeof rep === 'function') {
            value = rep.call(holder, key, value);
        }

// What happens next depends on the value's type.

        switch (typeof value) {
        case 'string':
            return quote(value);

        case 'number':

// JSON numbers must be finite. Encode non-finite numbers as null.

            return isFinite(value) 
                ? String(value) 
                : 'null';

        case 'boolean':
        case 'null':

// If the value is a boolean or null, convert it to a string. Note:
// typeof null does not produce 'null'. The case is included here in
// the remote chance that this gets fixed someday.

            return String(value);

// If the type is 'object', we might be dealing with an object or an array or
// null.

        case 'object':

// Due to a specification blunder in ECMAScript, typeof null is 'object',
// so watch out for that case.

            if (!value) {
                return 'null';
            }

// Make an array to hold the partial results of stringifying this object value.

            gap += indent;
            partial = [];

// Is the value an array?

            if (Object.prototype.toString.apply(value) === '[object Array]') {

// The value is an array. Stringify every element. Use null as a placeholder
// for non-JSON values.

                length = value.length;
                for (i = 0; i < length; i += 1) {
                    partial[i] = str(i, value) || 'null';
                }

// Join all of the elements together, separated with commas, and wrap them in
// brackets.

                v = partial.length === 0
                    ? '[]'
                    : gap
                        ? '[\n' + gap + partial.join(',\n' + gap) + '\n' + mind + ']'
                        : '[' + partial.join(',') + ']';
                gap = mind;
                return v;
            }

// If the replacer is an array, use it to select the members to be stringified.

            if (rep && typeof rep === 'object') {
                length = rep.length;
                for (i = 0; i < length; i += 1) {
                    if (typeof rep[i] === 'string') {
                        k = rep[i];
                        v = str(k, value);
                        if (v) {
                            partial.push(quote(k) + (
                                gap 
                                    ? ': ' 
                                    : ':'
                            ) + v);
                        }
                    }
                }
            } else {

// Otherwise, iterate through all of the keys in the object.

                for (k in value) {
                    if (Object.prototype.hasOwnProperty.call(value, k)) {
                        v = str(k, value);
                        if (v) {
                            partial.push(quote(k) + (
                                gap 
                                    ? ': ' 
                                    : ':'
                            ) + v);
                        }
                    }
                }
            }

// Join all of the member texts together, separated with commas,
// and wrap them in braces.

            v = partial.length === 0
                ? '{}'
                : gap
                    ? '{\n' + gap + partial.join(',\n' + gap) + '\n' + mind + '}'
                    : '{' + partial.join(',') + '}';
            gap = mind;
            return v;
        }
    }

// If the JSON object does not yet have a stringify method, give it one.

    if (typeof JSON.stringify !== 'function') {
        meta = {    // table of character substitutions
            '\b': '\\b',
            '\t': '\\t',
            '\n': '\\n',
            '\f': '\\f',
            '\r': '\\r',
            '"': '\\"',
            '\\': '\\\\'
        };
        JSON.stringify = function (value, replacer, space) {

// The stringify method takes a value and an optional replacer, and an optional
// space parameter, and returns a JSON text. The replacer can be a function
// that can replace values, or an array of strings that will select the keys.
// A default replacer method can be provided. Use of the space parameter can
// produce text that is more easily readable.

            var i;
            gap = '';
            indent = '';

// If the space parameter is a number, make an indent string containing that
// many spaces.

            if (typeof space === 'number') {
                for (i = 0; i < space; i += 1) {
                    indent += ' ';
                }

// If the space parameter is a string, it will be used as the indent string.

            } else if (typeof space === 'string') {
                indent = space;
            }

// If there is a replacer, it must be a function or an array.
// Otherwise, throw an error.

            rep = replacer;
            if (replacer && typeof replacer !== 'function' &&
                    (typeof replacer !== 'object' ||
                    typeof replacer.length !== 'number')) {
                throw new Error('JSON.stringify');
            }

// Make a fake root object containing our value under the key of ''.
// Return the result of stringifying the value.

            return str('', {'': value});
        };
    }


// If the JSON object does not yet have a parse method, give it one.

    if (typeof JSON.parse !== 'function') {
        JSON.parse = function (text, reviver) {

// The parse method takes a text and an optional reviver function, and returns
// a JavaScript value if the text is a valid JSON text.

            var j;

            function walk(holder, key) {

// The walk method is used to recursively walk the resulting structure so
// that modifications can be made.

                var k, v, value = holder[key];
                if (value && typeof value === 'object') {
                    for (k in value) {
                        if (Object.prototype.hasOwnProperty.call(value, k)) {
                            v = walk(value, k);
                            if (v !== undefined) {
                                value[k] = v;
                            } else {
                                delete value[k];
                            }
                        }
                    }
                }
                return reviver.call(holder, key, value);
            }


// Parsing happens in four stages. In the first stage, we replace certain
// Unicode characters with escape sequences. JavaScript handles many characters
// incorrectly, either silently deleting them, or treating them as line endings.

            text = String(text);
            rx_dangerous.lastIndex = 0;
            if (rx_dangerous.test(text)) {
                text = text.replace(rx_dangerous, function (a) {
                    return '\\u' +
                            ('0000' + a.charCodeAt(0).toString(16)).slice(-4);
                });
            }

// In the second stage, we run the text against regular expressions that look
// for non-JSON patterns. We are especially concerned with '()' and 'new'
// because they can cause invocation, and '=' because it can cause mutation.
// But just to be safe, we want to reject all unexpected forms.

// We split the second stage into 4 regexp operations in order to work around
// crippling inefficiencies in IE's and Safari's regexp engines. First we
// replace the JSON backslash pairs with '@' (a non-JSON character). Second, we
// replace all simple value tokens with ']' characters. Third, we delete all
// open brackets that follow a colon or comma or that begin the text. Finally,
// we look to see that the remaining characters are only whitespace or ']' or
// ',' or ':' or '{' or '}'. If that is so, then the text is safe for eval.

            if (
                rx_one.test(
                    text
                        .replace(rx_two, '@')
                        .replace(rx_three, ']')
                        .replace(rx_four, '')
                )
            ) {

// In the third stage we use the eval function to compile the text into a
// JavaScript structure. The '{' operator is subject to a syntactic ambiguity
// in JavaScript: it can begin a block or an object literal. We wrap the text
// in parens to eliminate the ambiguity.

                j = eval('(' + text + ')');

// In the optional fourth stage, we recursively walk the new structure, passing
// each name/value pair to a reviver function for possible transformation.

                return typeof reviver === 'function'
                    ? walk({'': j}, '')
                    : j;
            }

// If the text is not JSON parseable, then a SyntaxError is thrown.

            throw new SyntaxError('JSON.parse');
        };
    }
}());

//Provides: caml_json
//Requires: JSON
function caml_json() { return JSON; }

//# 1 "bigstring.js"
///////// BIGSTRING
//Provides: bigstring_alloc
//Requires: caml_ba_create
function bigstring_alloc(_,size){
  return caml_ba_create(12, 0, [0,size]);
}

//Provides: bigstring_destroy_stub
function bigstring_destroy_stub(_v) {
  return 0; // noop
}

//Provides: bigstring_blit_bigstring_bytes_stub
//Requires: caml_bytes_set, caml_ba_get_1
function bigstring_blit_bigstring_bytes_stub(v_bstr, v_src_pos, v_str, v_dst_pos, v_len){
  for(var i = 0; i < v_len; i++){
    var c = caml_ba_get_1(v_bstr,v_src_pos + i);
    caml_bytes_set(v_str,v_dst_pos + i,c);
  }
  return 0;
}

//Provides: bigstring_blit_bigstring_string_stub
//Requires: bigstring_blit_bigstring_bytes_stub
var bigstring_blit_bigstring_string_stub = bigstring_blit_bigstring_bytes_stub

//Provides: caml_blit_bigstring_to_string
//Requires: bigstring_blit_bigstring_bytes_stub
var caml_blit_bigstring_to_string = bigstring_blit_bigstring_bytes_stub

//Provides: bigstring_blit_string_bigstring_stub
//Requires: caml_string_get, caml_ba_set_1
function bigstring_blit_string_bigstring_stub(v_str, v_src_pos, v_bstr, v_dst_pos, v_len){
  for (var i = 0; i < v_len; i++) caml_ba_set_1(v_bstr,v_dst_pos + i,caml_string_get(v_str,v_src_pos + i));
  return 0;
}

//Provides: bigstring_blit_bytes_bigstring_stub
//Requires: caml_bytes_get, caml_ba_set_1
function bigstring_blit_bytes_bigstring_stub(v_str, v_src_pos, v_bstr, v_dst_pos, v_len){
  for (var i = 0; i < v_len; i++) caml_ba_set_1(v_bstr,v_dst_pos + i,caml_bytes_get(v_str,v_src_pos + i));
  return 0;
}
//Provides: caml_blit_string_to_bigstring
//Requires: bigstring_blit_string_bigstring_stub
var caml_blit_string_to_bigstring = bigstring_blit_string_bigstring_stub

//Provides: bigstring_blit_stub
//Requires: caml_ba_get_1, caml_ba_set_1
function bigstring_blit_stub(s1, i1, s2, i2, len){
  for (var i = 0; i < len; i++) caml_ba_set_1(s2,i2 + i,caml_ba_get_1(s1,i1 + i));
  return 0;
}

//Provides: bigstring_memcmp_stub
//Requires: caml_ba_get_1
function bigstring_memcmp_stub(v_s1, v_s1_pos, v_s2, v_s2_pos, v_len){
  for (var i = 0; i < v_len; i++) {
    var a = caml_ba_get_1(v_s1,v_s1_pos + i);
    var b = caml_ba_get_1(v_s2,v_s2_pos + i);
    if (a < b) return -1;
    if (a > b) return 1;
  }
  return 0;
}

//Provides: bigstring_find
//Requires: caml_ba_get_1
function bigstring_find(bs, chr, pos, len){
  while(len > 0){
    if(caml_ba_get_1(bs,pos) == chr) return pos;
    pos++;
    len--;
  }
  return -1;
}

//Provides: bigstring_to_array_buffer mutable
function bigstring_to_array_buffer(bs) {
  return bs.data.buffer
}

//Provides: bigstring_of_array_buffer mutable
//Requires: caml_ba_create_from
function bigstring_of_array_buffer(ab) {
  var ta = new joo_global_object.Uint8Array(ab);
  return caml_ba_create_from(ta, null, 0, 12, 0, [ta.length])
}

//Provides: bigstring_marshal_data_size_stub mutable
//Requires: caml_failwith, caml_ba_uint8_get32
function bigstring_marshal_data_size_stub (s, ofs) {
  if (caml_ba_uint8_get32(s, ofs) != (0x8495A6BE|0))
    caml_failwith("Marshal.data_size: bad object");
  return (caml_ba_uint8_get32(s, ofs + 4));
}

//Provides: bigstring_unmarshal_stub mutable
//Requires: BigStringReader, caml_input_value_from_reader
function bigstring_unmarshal_stub(s,ofs) {
  var reader = new BigStringReader (s, typeof ofs=="number"?ofs:ofs[0]);
  return caml_input_value_from_reader(reader, ofs)
}


//Provides: bigstring_marshal_stub mutable
//Requires: caml_output_val, bigstring_alloc, caml_ba_set_1
function bigstring_marshal_stub (v, _fl) {
  /* ignores flags... */
  var arr = caml_output_val (v);
  var bs  = bigstring_alloc(0,arr.length);
  for(var i = 0; i < arr.length; i++){
    caml_ba_set_1(bs, i, arr[i]);
  }
  return bs;
}

//Provides: bigstring_marshal_blit_stub
//Requires: caml_output_val, caml_failwith, caml_ba_set_1
function bigstring_marshal_blit_stub (s, ofs, len, v, _fl) {
  /* ignores flags... */
  var t = caml_output_val (v);
  if (t.length > len) caml_failwith ("Marshal.to_buffer: buffer overflow");
  for(var i = 0; i < t.length; i++){
    caml_ba_set_1(s, (i + ofs), t[i]);
  }
  return t.length;
}

//Provides: caml_hash_mix_bigstring
//Requires: caml_hash_mix_string_arr
function caml_hash_mix_bigstring(h, bs) {
    return caml_hash_mix_string_arr(h,bs.data);
}

//# 1 "weak.js"
// Js_of_ocaml runtime support
// http://www.ocsigen.org/js_of_ocaml/
// Copyright (C) 2010 Jérôme Vouillon
// Laboratoire PPS - CNRS Université Paris Diderot
//
// This program is free software; you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, with linking exception;
// either version 2.1 of the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with this program; if not, write to the Free Software
// Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

// Weak API, but without the weak semantics

//Provides: caml_ephe_key_offset
//Version: < 4.03
var caml_ephe_key_offset = 2

//Provides: caml_ephe_key_offset
//Version: >= 4.03
var caml_ephe_key_offset = 3

//Provides: caml_ephe_data_offset
//Version: >= 4.03
var caml_ephe_data_offset = 2

//Provides: caml_weak_create
//Requires: caml_ephe_key_offset, caml_invalid_argument
function caml_weak_create (n) {
  if (n < 0) caml_invalid_argument ("Weak.create");
  var x = [251,"caml_ephe_list_head"];
  x.length = caml_ephe_key_offset + n;
  return x;
}
//Provides: caml_weak_set
//Requires: caml_ephe_key_offset, caml_invalid_argument
function caml_weak_set(x, i, v) {
    if(i < 0 || caml_ephe_key_offset + i >= x.length)
      caml_invalid_argument ("Weak.set");
    x[caml_ephe_key_offset + i] = v;
    return 0;
}
//Provides: caml_weak_get
//Requires: caml_ephe_key_offset, caml_invalid_argument
function caml_weak_get(x, i) {
    if(i < 0 || caml_ephe_key_offset + i >= x.length)
      caml_invalid_argument ("Weak.get_key");
    return (x[caml_ephe_key_offset + i ]===undefined)?0:x[caml_ephe_key_offset + i];
}
//Provides: caml_weak_get_copy
//Requires: caml_weak_get,caml_ephe_key_offset
//Requires: caml_obj_dup, caml_invalid_argument
function caml_weak_get_copy(x, i) {
  if(i < 0 || caml_ephe_key_offset + i >= x.length)
    caml_invalid_argument ("Weak.get_copy");
  var y = caml_weak_get(x, i);
  if (y === 0) return y;
  var z = y[1];
  if (z instanceof Array) return [0, caml_obj_dup(z)];
  return y;
}
//Provides: caml_weak_check mutable
//Requires: caml_ephe_key_offset
function caml_weak_check(x, i) {
  if(x[caml_ephe_key_offset + i]!==undefined && x[caml_ephe_key_offset + i] !==0)
    return 1;
  else
    return 0;
}

//Provides: caml_weak_blit
//Requires: caml_array_blit
//Requires: caml_ephe_key_offset
function caml_weak_blit(a1, i1, a2, i2, len) {
  // minus one because caml_array_blit works on ocaml array
  caml_array_blit(a1, caml_ephe_key_offset + i1 - 1,
                  a2, caml_ephe_key_offset + i2 - 1,
                  len);
  return 0;
}

//Provides: caml_ephe_create
//Requires: caml_weak_create
var caml_ephe_create = caml_weak_create

//Provides: caml_ephe_blit_key
//Requires: caml_weak_blit
var caml_ephe_blit_key = caml_weak_blit

//Provides: caml_ephe_get_key
//Requires: caml_weak_get
var caml_ephe_get_key = caml_weak_get

//Provides: caml_ephe_get_key_copy
//Requires: caml_weak_get_copy
var caml_ephe_get_key_copy = caml_weak_get_copy

//Provides: caml_ephe_check_key
//Requires: caml_weak_check
var caml_ephe_check_key = caml_weak_check

//Provides: caml_ephe_set_key
//Requires: caml_weak_set
function caml_ephe_set_key(x, i, v) {
  return caml_weak_set(x, i, [0, v])
}

//Provides: caml_ephe_unset_key
//Requires: caml_weak_set
function caml_ephe_unset_key(x, i) {
  return caml_weak_set(x, i, 0)
}

//Provides: caml_ephe_blit_data
//Requires: caml_ephe_data_offset
//Version: >= 4.03
function caml_ephe_blit_data(src, dst){
  dst[caml_ephe_data_offset] = src[caml_ephe_data_offset];
  return 0;
}

//Provides: caml_ephe_get_data
//Requires: caml_ephe_data_offset
//Version: >= 4.03
function caml_ephe_get_data(x){
  if(x[caml_ephe_data_offset] === undefined)
    return 0;
  else
    return [0, x[caml_ephe_data_offset]];
}

//Provides: caml_ephe_get_data_copy
//Requires: caml_ephe_data_offset
//Requires: caml_obj_dup
//Version: >= 4.03
function caml_ephe_get_data_copy(x){
  if(x[caml_ephe_data_offset] === undefined)
    return 0;
  else
    return [0, caml_obj_dup(x[caml_ephe_data_offset])];
}

//Provides: caml_ephe_set_data
//Requires: caml_ephe_data_offset
//Version: >= 4.03
function caml_ephe_set_data(x, data){
  x[caml_ephe_data_offset] = data;
  return 0;
}

//Provides: caml_ephe_unset_data
//Requires: caml_ephe_data_offset
//Version: >= 4.03
function caml_ephe_unset_data(x, data){
  x[caml_ephe_data_offset] = undefined;
  return 0;
}

//Provides: caml_ephe_check_data
//Requires: caml_ephe_data_offset
//Version: >= 4.03
function caml_ephe_check_data(x){
  if(x[caml_ephe_data_offset] === undefined)
    return 0;
  else
    return 1;
}

