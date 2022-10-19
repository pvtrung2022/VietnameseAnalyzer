package vietnameseanalyze;

import com.trung.ExprConvertible;
import com.wolfram.jlink.Expr;
import com.trung.LoopbackLink;

import java.util.Objects;

public final class SegmentWord implements ExprConvertible
{
    public String Word = null;
    public String Type = null;
    public int Start = -1;
    public int End = -1;

    public SegmentWord(String word, String type, int start, int end)
    {
        this.Word = word;
        this.Type = type;
        this.Start = start;
        this.End = end;
    }

    @Override
    public String toString()
    {
        return "SegmentWord[" + Word + "," + Type + "," + Start + "," + End + ']';
    }

    @Override
    public boolean equals(Object o)
    {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        SegmentWord that = (SegmentWord) o;
        return Start == that.Start && End == that.End && Objects.equals(Word, that.Word) && Objects.equals(Type, that.Type);
    }

    @Override
    public int hashCode()
    {
        return Objects.hash(Word, Type, Start, End);
    }

    @Override
    public Expr toExpr()
    {
        var loopBack = new LoopbackLink();
        loopBack.putFunction("SegmentWord", 4);
        loopBack.put(this.Word);
        loopBack.put(this.Type);
        loopBack.put(this.Start);
        loopBack.put(this.End);
        return loopBack.getExpr();
    }
}
