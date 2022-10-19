package vietnameseanalyze;

import java.util.ArrayList;
import java.util.Collection;

public class CustomArrayList<T> extends ArrayList<T>
{

    public CustomArrayList(T[] initialEles)
    {
        super();
        for (var ele : initialEles)
            this.add(ele);
    }
}
