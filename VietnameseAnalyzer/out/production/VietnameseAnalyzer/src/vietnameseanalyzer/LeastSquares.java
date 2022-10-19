package vietnameseanalyzer;

import java.util.ArrayList;
import java.util.HashMap;

public class LeastSquares
{

    public ArrayList<Double> Single;
    public double SingleVariance;
    public ArrayList<Double> Left;
    public double LeftVariance;
    public ArrayList<Double> Right;
    public double RightVariance;
    public ArrayList<Double> Between;
    public double BetweenVariance;

    @Override
    public String toString()
    {

        var show = new HashMap<String, Object>();
        show.put("Single", this.Single);
        show.put("Left", this.Left);
        show.put("Right", this.Right);
        show.put("Between", this.Between);
        return show.toString();
    }
}
