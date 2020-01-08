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

import java.util.Arrays;
import java.util.List;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TreeSet;
import java.time.*;
import java.time.format.DateTimeFormatter;

import com.google.gson.*;

public class SqlDateComponent {
    public final static String YEAR = "YEAR";
    public final static String MONTH = "MONTH";
    public final static String DAY = "DAY";

    /* Utilities */
    private static JsonElement boxDate(LocalDate d) {
        JsonObject result = new JsonObject();
        JsonObject resultIn = new JsonObject();
        JsonObject resultIn2 = new JsonObject();
        resultIn2.add("year",new JsonPrimitive(d.getYear()));
        resultIn2.add("month",new JsonPrimitive(d.getMonthValue()));
        resultIn2.add("day",new JsonPrimitive(d.getDayOfMonth()));
        resultIn.add("$date", resultIn2);
        result.add("$foreign", resultIn);
        return result;
    }

    private static JsonObject getDate(JsonElement e) {
        return ((JsonObject) ((JsonObject) ((JsonObject)e).get("$foreign")).get("$date"));
    }
    private static LocalDate unboxDate(JsonElement e) {
        int year = getDate(e).get("year").getAsInt();
        int month = getDate(e).get("month").getAsInt();
        int day = getDate(e).get("day").getAsInt();
        return LocalDate.of(year, month, day);
    }

    private static JsonElement boxPeriod(Period p) {
        JsonObject result = new JsonObject();
        JsonObject resultIn = new JsonObject();
        JsonObject resultIn2 = new JsonObject();
        resultIn2.add("unit",new JsonPrimitive(DAY));
        resultIn2.add("period",new JsonPrimitive(p.getDays()));
        resultIn.add("$period", resultIn2);
        result.add("$foreign", resultIn);
        return result;
    }

    private static JsonObject getPeriod(JsonElement e) {
        return ((JsonObject) ((JsonObject) ((JsonObject)e).get("$foreign")).get("period"));
    }
    private static Period unboxPeriod(JsonElement e) {
        String unit = getPeriod(e).get("unit").getAsString();
        int period = getPeriod(e).get("period").getAsInt();
        Period result;
        switch (unit) {
        case YEAR:
            result = Period.ofYears(period);
            break;
        case MONTH:
            result = Period.ofMonths(period);
            break;
        case DAY:
            result = Period.ofDays(period);
            break;
        default:
            throw new RuntimeException("Unknown period unit: " + unit);
        }
        return result;
    }

    /* Operators */
    public static JsonElement sql_date_get_component(String part, JsonElement e) {
        LocalDate d = unboxDate(e);
        JsonPrimitive result;
        switch (part) {
        case YEAR:
            result = new JsonPrimitive(d.getYear());
            break;
        case MONTH:
            result = new JsonPrimitive(d.getMonthValue());
            break;
        case DAY:
            result = new JsonPrimitive(d.getDayOfMonth());
            break;
        default:
            throw new RuntimeException("Unknown date component: " + part);
        }
        return UnaryOperators.rec("$nat",result);
    }

    public static JsonElement sql_date_from_string(JsonElement e) {
        final String str = e.getAsString();
        return boxDate(LocalDate.parse(str));
    }

    public static JsonElement sql_date_period_from_string(JsonElement e) {
        final String str = e.getAsString();
        // XXX TODO extract period here
        return boxPeriod(Period.parse("P1D"));
    }

    public static JsonElement sql_date_plus(JsonElement e1, JsonElement e2) {
        LocalDate d1 = unboxDate(e1);
        Period p2 = unboxPeriod(e2);
        return boxDate(d1.plus(p2));
    }

    public static JsonElement sql_date_minus(JsonElement e1, JsonElement e2) {
        LocalDate d1 = unboxDate(e1);
        Period p2 = unboxPeriod(e2);
        return boxDate(d1.minus(p2));
    }

    public static JsonPrimitive sql_date_ne(JsonElement e1, JsonElement e2) {
        LocalDate d1 = unboxDate(e1);
        LocalDate d2 = unboxDate(e2);
        return new JsonPrimitive(!d1.isEqual(d2));
    }

    public static JsonPrimitive sql_date_lt(JsonElement e1, JsonElement e2) {
        LocalDate d1 = unboxDate(e1);
        LocalDate d2 = unboxDate(e2);
        return new JsonPrimitive(d1.isBefore(d2));
    }

    public static JsonPrimitive sql_date_le(JsonElement e1, JsonElement e2) {
        LocalDate d1 = unboxDate(e1);
        LocalDate d2 = unboxDate(e2);
        return new JsonPrimitive(d1.isBefore(d2) || d1.isEqual(d2));
    }

    public static JsonPrimitive sql_date_gt(JsonElement e1, JsonElement e2) {
        LocalDate d1 = unboxDate(e1);
        LocalDate d2 = unboxDate(e2);
        return new JsonPrimitive(d1.isAfter(d2));
    }

    public static JsonPrimitive sql_date_ge(JsonElement e1, JsonElement e2) {
        LocalDate d1 = unboxDate(e1);
        LocalDate d2 = unboxDate(e2);
        return new JsonPrimitive(d1.isAfter(d2) || d1.isEqual(d2));
    }

    public static JsonElement sql_date_period_between(JsonElement e1, JsonElement e2) {
        LocalDate d1 = unboxDate(e1);
        LocalDate d2 = unboxDate(e2);
        return boxPeriod(Period.between(d1, d2));
    }
}
