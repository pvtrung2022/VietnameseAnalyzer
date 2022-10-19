package vietnameseanalyzer;

import com.trung.Graph;

import java.util.ArrayList;
import java.util.HashSet;

public class Parser extends Graph<WordVertex>
{
    public HashSet<ArrayList<WordVertex>> MeaningSupplementEdges = new HashSet<>();

    public void deleteMeaningSupplementEdges()
    {
        this.deleteEdges(this.MeaningSupplementEdges);
        this.MeaningSupplementEdges.clear();
    }

    public Parser()
    {
        super();
    }

    public Parser(Graph<WordVertex> g)
    {
        this.addVertices(g.vertexList());
        this.addEdges(g.edgeList());
    }

    @Override
    public Parser clone()
    {
        var res = (Parser) super.clone();
        res.MeaningSupplementEdges = (HashSet<ArrayList<WordVertex>>) this.MeaningSupplementEdges.clone();
        return res;
    }
}
