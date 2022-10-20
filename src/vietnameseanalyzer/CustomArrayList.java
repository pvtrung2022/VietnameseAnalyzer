package vietnameseanalyzer;

import java.util.ArrayList;

public class CustomArrayList<T> extends ArrayList<T>
{

    public CustomArrayList(T[] initialEles)
    {
        super();
        for (var ele : initialEles)
            this.add(ele);
    }
}
