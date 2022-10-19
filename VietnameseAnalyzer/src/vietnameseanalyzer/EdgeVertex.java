package vietnameseanalyzer;

import java.util.ArrayList;
import java.util.Objects;

public class EdgeVertex
{
    public ArrayList<String> Tail;
    public ArrayList<String> Head;
    public String Direction = null;
//    public boolean isSink = false;

    public EdgeVertex(ArrayList<String> tail, ArrayList<String> head)
    {
        this.Tail = tail;
        this.Head = head;
    }

    @Override
    public String toString()
    {

        return "EdgeVertex[" +
                "Tail=" + Tail +
                ", Head=" + Head +
                ", Direction='" + Direction + '\'' +
                ']';

    }

    @Override
    public boolean equals(Object o)
    {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        EdgeVertex that = (EdgeVertex) o;
        return Objects.equals(Tail, that.Tail) && Objects.equals(Head, that.Head) && Objects.equals(Direction, that.Direction);
    }

    @Override
    public int hashCode()
    {
        return Objects.hash(Tail, Head, Direction);
    }
}
