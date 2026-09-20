using System;
using System.Collections;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text;
using System.Text.Json;
using Dafny;

namespace BenchmarkOutput {
  public static class Capture {
    private static JsonDocument input;
    private static MemoryStream output;
    private static Utf8JsonWriter writer;

    public static bool NextCase() {
      var line = Console.ReadLine();
      if (line == null) return false;
      input?.Dispose();
      input = JsonDocument.Parse(line);
      return true;
    }

    private static JsonElement Argument(BigInteger index) =>
      input.RootElement.GetProperty("inputs")[(int)index];

    public static BigInteger ReadInt(BigInteger index) =>
      BigInteger.Parse(Argument(index).GetRawText(), CultureInfo.InvariantCulture);
    public static ISequence<Dafny.Rune> ReadString(BigInteger index) =>
      Sequence<Dafny.Rune>.UnicodeFromString(Argument(index).GetString());
    public static ISequence<BigInteger> ReadInts(BigInteger index) =>
      Sequence<BigInteger>.FromArray(Argument(index).EnumerateArray().Select(
        item => BigInteger.Parse(item.GetRawText(), CultureInfo.InvariantCulture)).ToArray());
    public static ISequence<ISequence<Dafny.Rune>> ReadStrings(BigInteger index) =>
      Sequence<ISequence<Dafny.Rune>>.FromArray(Argument(index).EnumerateArray().Select(
        item => Sequence<Dafny.Rune>.UnicodeFromString(item.GetString())).ToArray());

    public static void Begin() {
      output = new MemoryStream();
      writer = new Utf8JsonWriter(output);
      writer.WriteStartArray();
    }

    public static void Emit<T>(T value) => WriteValue(value);

    private static void WriteValue(object value) {
      if (value is BigInteger integer) {
        writer.WriteRawValue(integer.ToString(CultureInfo.InvariantCulture));
      } else if (value is bool boolean) {
        writer.WriteBooleanValue(boolean);
      } else if (value is ISequence<Dafny.Rune> runes) {
        writer.WriteStringValue(string.Concat(runes.Select(rune => rune.ToString())));
      } else if (value is ISequence<char> chars) {
        writer.WriteStringValue(new string(chars.ToArray()));
      } else if (value is string text) {
        writer.WriteStringValue(text);
      } else if (value is IEnumerable sequence) {
        writer.WriteStartArray();
        foreach (var item in sequence) WriteValue(item);
        writer.WriteEndArray();
      } else {
        throw new InvalidOperationException("Unsupported algorithm output type");
      }
    }

    public static void End() {
      writer.WriteEndArray();
      writer.Flush();
      Console.WriteLine("\nCASE " + input.RootElement.GetProperty("index").GetInt32() +
                        " OUTPUT " + Encoding.UTF8.GetString(output.ToArray()));
      writer.Dispose();
      output.Dispose();
    }

    public static void Result(bool passed) {
      Console.WriteLine("\nCASE " + input.RootElement.GetProperty("index").GetInt32() +
                        (passed ? " PASS" : " FAIL"));
    }
  }
}
