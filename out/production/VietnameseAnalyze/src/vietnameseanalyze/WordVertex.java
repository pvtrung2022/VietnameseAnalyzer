package vietnameseanalyze;

import com.trung.ExprConvertible;
import com.trung.LoopbackLink;
import com.wolfram.jlink.Expr;

import java.util.Objects;

public final class WordVertex implements ExprConvertible
{
    public int Location = -1;
    public String Word = null;
    public String Type = null;

    public boolean isMarked = false;
    public boolean isProcessedVertex = false;
    public boolean isAdditionalProcessedVertex = false;

    public void resetAdditionalProperties()
    {
        this.isMarked = false;
        this.isProcessedVertex = false;
        this.isAdditionalProcessedVertex = false;
    }

    @Override
    protected Object clone()
    {
        var res = new WordVertex(this.Location, this.Word, this.Type);
        return res;
    }

    public WordVertex(int loc, String word, String type)
    {
        this.Location = loc;
        this.Word = word;
        this.Type = type;
    }

    @Override
    public boolean equals(Object o)
    {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        WordVertex that = (WordVertex) o;
        return Location == that.Location && Word.equals(that.Word) && Type.equals(that.Type);
    }

    @Override
    public int hashCode()
    {
        return Objects.hash(Location, Word, Type);
    }

    @Override
    public String toString()
    {
        return "[" + this.Location + "," + this.Word + "," + this.Type + "]";
    }

    @Override
    public Expr toExpr()
    {
        var loopbackLink=new LoopbackLink();
        loopbackLink.putFunction("WordVertex",3);
        loopbackLink.put(this.Location);
        loopbackLink.put(this.Word);
        loopbackLink.put(this.Type);
        return loopbackLink.getExpr();
    }
}
