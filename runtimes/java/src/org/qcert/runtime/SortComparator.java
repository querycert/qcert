/*
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.qcert.runtime;

import java.util.Comparator;
import java.util.Map.Entry;

import com.google.gson.*;

/*
 * Comparator for order by
 */
public final class SortComparator implements Comparator<JsonElement> {
    private static DataComparator datacomparator = DataComparator.getComparator();

    private Object[] sortCriterias;

    public int compare(JsonElement e1, JsonElement e2) {
        JsonObject o1 = e1.getAsJsonObject();
        JsonObject o2 = e2.getAsJsonObject();

        int result = 0;

        // iterating over an array
        for (int i = 0; i < sortCriterias.length; i++) {
            Entry<String, RuntimeUtils.SortDesc> sortCrit = (Entry<String, RuntimeUtils.SortDesc>) sortCriterias[i];
            result = datacomparator.compare(o1.get(sortCrit.getKey()), o2.get(sortCrit.getKey()));
            if (result != 0) {
                return result;
            }
        }
        return result;
    }

    public static DataComparator getComparator() {
        return datacomparator;
    }

    public SortComparator(Object[] sortCriterias) {
        this.sortCriterias = sortCriterias;
    }

}
