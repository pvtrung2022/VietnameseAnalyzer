package vietnameseanalyze;

import java.util.HashMap;

public class CustomHashMap<S, T> extends HashMap<S, T>
{
    public CustomHashMap(Object[][] corres)
    {
        super();
        for (var i = 0; i <= corres.length - 1; i++)
        {
            var iRow = corres[i];
            var key = iRow[0];
            var Scl = (Class<S>) key.getClass();
            var value = iRow[1];
            var Tcl = (Class<T>) value.getClass();
            this.put(Scl.cast(key), Tcl.cast(value));
        }
    }
}
