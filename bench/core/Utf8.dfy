include "World.dfy"

module Utf8Semantics {
  import BW = BenchWorld

  predicate UnicodeScalar(ch: char)
  {
    var code := ch as int;
    0 <= code <= 0x10ffff && !(0xd800 <= code <= 0xdfff)
  }

  // External argv/path values are scalar strings without NUL; invalid raw POSIX byte strings are unrepresentable.
  predicate ValidExternalText(text: string)
  {
    forall i | 0 <= i < |text| ::
      text[i] != '\0' && UnicodeScalar(text[i])
  }

  function EncodeChar(ch: char): BW.Bytes
    ensures |EncodeChar(ch)| == BW.Utf8ByteWidth(ch)
    ensures 1 <= |EncodeChar(ch)| <= 4
  {
    var code := ch as int;
    if code <= 0x7f then
      [code as char]
    else if code <= 0x7ff then
      [
        (0xc0 + code / 0x40) as char,
        (0x80 + code % 0x40) as char
      ]
    else if code <= 0xffff then
      [
        (0xe0 + code / 0x1000) as char,
        (0x80 + (code / 0x40) % 0x40) as char,
        (0x80 + code % 0x40) as char
      ]
    else
      [
        (0xf0 + code / 0x40000) as char,
        (0x80 + (code / 0x1000) % 0x40) as char,
        (0x80 + (code / 0x40) % 0x40) as char,
        (0x80 + code % 0x40) as char
      ]
  }

  function EncodeFrom(text: string, i: nat): BW.Bytes
    requires i <= |text|
  {
    Encode(text[i..])
  }

  function Encode(text: string): BW.Bytes
    ensures |Encode(text)| >= |text|
    decreases |text|
  {
    if text == [] then [] else EncodeChar(text[0]) + Encode(text[1..])
  }

  lemma EncodeConcat(left: string, right: string)
    ensures Encode(left + right) == Encode(left) + Encode(right)
    decreases |left|
  {
    if left != [] {
      EncodeConcat(left[1..], right);
      assert (left + right)[0] == left[0];
      assert (left + right)[1..] == left[1..] + right;
      calc {
        Encode(left + right);
        EncodeChar(left[0]) + Encode(left[1..] + right);
        EncodeChar(left[0]) + (Encode(left[1..]) + Encode(right));
        (EncodeChar(left[0]) + Encode(left[1..])) + Encode(right);
        Encode(left) + Encode(right);
      }
    } else {
      assert left + right == right;
      assert Encode(left) == [];
      assert Encode(left) + Encode(right) == Encode(right);
    }
  }

  lemma EncodeLength(text: string)
    ensures |Encode(text)| == BW.Utf8ByteLength(text)
    decreases |text|
  {
    if text != [] {
      EncodeLength(text[1..]);
    }
  }
}
