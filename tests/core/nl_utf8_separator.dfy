include "../../bench/utils/nl/NlSpec.dfy"

module NlUtf8SeparatorRegression {
  import S = NlSchema
  import N = NlSpec
  import U = Utf8Semantics
  import W = BenchWorld

  function Command(separator: string): S.NlCmd
  {
    S.NlCmd(S.ModeRun, S.NumberNonEmpty, S.FormatRight, separator, [], [S.Stdin])
  }

  // Repeating a space produces exactly the requested number of bytes.
  lemma SpacesLength(count: nat)
    ensures |N.RepeatChar(' ', count)| == count
    decreases count
  {
    if count > 0 {
      SpacesLength(count - 1);
    }
  }

  // Every separator is encoded without restricting text to byte characters.
  lemma ArbitrarySeparator(cmd: S.NlCmd, number: nat)
    ensures N.LineNumberText(cmd, number) ==
            N.RenderNumber(cmd.numberFormat, number, 6) + U.Encode(cmd.separator)
    ensures |N.BlankPrefix(cmd)| == 6 + |U.Encode(cmd.separator)|
    ensures N.LinePrefix(cmd.(bodyStyle := S.NumberAll), false, number) ==
            N.RenderNumber(cmd.numberFormat, number, 6) + U.Encode(cmd.separator)
    ensures N.LinePrefix(cmd.(bodyStyle := S.NumberNone), true, number) ==
            N.RepeatChar(' ', 6 + |U.Encode(cmd.separator)|)
  {
    SpacesLength(6 + |U.Encode(cmd.separator)|);
  }

  // An empty separator leaves exactly the six-column number field.
  lemma {:fuel N.RepeatChar, 16, 17} {:fuel U.Encode, 6, 7} EmptySeparator()
    ensures N.LineRenderRelation(Command(""), "x", true, 1, "     1x\n")
    ensures N.BlankPrefix(Command("")) == "      "
  {
  }

  // An ASCII separator preserves its bytes and counts each byte in blank padding.
  lemma {:fuel N.RepeatChar, 16, 17} {:fuel U.Encode, 6, 7} AsciiSeparator()
    ensures N.LineRenderRelation(Command(": "), "x", true, 1, "     1: x\n")
    ensures N.BlankPrefix(Command(": ")) == "        "
  {
  }

  // A Latin separator expands to two UTF-8 bytes on numbered and blank lines.
  lemma {:fuel N.RepeatChar, 16, 17} {:fuel U.Encode, 6, 7} LatinSeparator()
    ensures N.LineRenderRelation(Command("é"), "x", true, 1,
                                 "     1" + [(0xc3 as char), (0xa9 as char)] + "x\n")
    ensures N.LineRenderRelation(Command("é"), [], true, 1, "        \n")
  {
  }

  // A CJK separator uses three bytes even though it is one character.
  lemma {:fuel N.RepeatChar, 16, 17} {:fuel U.Encode, 6, 7} CjkSeparator()
    ensures N.LineRenderRelation(Command("한"), "x", true, 1,
                                 "     1" + [(0xed as char), (0x95 as char), (0x9c as char)] + "x\n")
    ensures N.LineRenderRelation(Command("한"), [], true, 1, "         \n")
  {
  }

  // A non-BMP separator remains representable as four UTF-8 bytes.
  lemma {:fuel N.RepeatChar, 16, 17} {:fuel U.Encode, 6, 7} NonBmpSeparator()
    ensures N.LineRenderRelation(Command("😀"), "x", true, 1,
                                 "     1" + [(0xf0 as char), (0x9f as char), (0x98 as char), (0x80 as char)] + "x\n")
    ensures N.LineRenderRelation(Command("😀"), [], true, 1, "          \n")
  {
  }

  // Mixed separator text preserves order and sums encoded widths.
  lemma {:fuel N.RepeatChar, 16, 17} {:fuel U.Encode, 6, 7} MixedSeparator()
    ensures N.LineRenderRelation(Command(":é한😀"), "x", false, 1,
                                 "     1:" + [(0xc3 as char), (0xa9 as char), (0xed as char), (0x95 as char),
                                              (0x9c as char), (0xf0 as char), (0x9f as char), (0x98 as char),
                                              (0x80 as char)] + "x")
    ensures |N.BlankPrefix(Command(":é한😀"))| == 16
  {
    assert U.Encode(":é한😀") ==
           [':' as char, (0xc3 as char), (0xa9 as char), (0xed as char), (0x95 as char),
            (0x9c as char), (0xf0 as char), (0x9f as char), (0x98 as char), (0x80 as char)];
    assert N.RenderNumber(S.FormatRight, 1, 6) == "     1";
    SpacesLength(16);
  }

  // Left and zero-padded number formats retain the same encoded separator.
  lemma {:fuel N.RepeatChar, 16, 17} {:fuel U.Encode, 6, 7} NumberFormats()
    ensures N.LineNumberText(Command("é").(numberFormat := S.FormatLeft), 1) ==
            "1     " + [(0xc3 as char), (0xa9 as char)]
    ensures N.LineNumberText(Command("é").(numberFormat := S.FormatRightZero), 1) ==
            "000001" + [(0xc3 as char), (0xa9 as char)]
  {
  }
}
