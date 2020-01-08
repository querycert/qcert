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

/* JavaScript runtime for SqlDate component */

/* Utilities */
var DAY = "DAY";
var MONTH = "MONTH";
var YEAR = "YEAR";

function boxDate(year, month, day) {
    return { "$foreign" : { "$date" : { "day": day, "month": month, "year": year } } };
}

function mustBeDate(date) {
    if ("$foreign" in date && "$date" in date["$foreign"]) {
        var d = date.$foreign.$date;
        if (typeof d === "object" && "year" in d && "month" in d && "day" in d)
	          return d;
    }
    throw new Error("Expected a date but got " + JSON.stringify(date));
}

function mustBeUnit(unit) {
    if (unit === DAY || unit === MONTH || unit === YEAR)
	      return;
    throw new Error("Expected a period unit but got " + JSON.stringify(unit));
}

function mustBePeriod(period) {
    if (period.$foreign && period.$foreign.$interval) {
        var i = period.$foreign.$interval;
        if (typeof i === "object" && "period" in i && "unit" in i) {
	          mustBeUnit(i.unit);
	          return i;
        }
    }
    throw new Error("Expected a period but got " + JSON.stringify(period));
}

function compareDates(date1, date2) {
    if (date1.year < date2.year)
	      return -1;
    if (date1.year > date2.year)
	      return 1;
    if (date1.month < date2.month)
	      return -1;
    if (date1.month > date2.month)
	      return 1;
    if (date1.day < date2.day)
	      return -1;
    if (date1.day > date2.day)
	      return 1;
    return 0;
}

/* Date */
function dateFromString(stringDate) {
    if (typeof stringDate === "string") {
	      parts = stringDate.split("-");
	      if (parts.length === 3) {
            return boxDate(Number(parts[0]), Number(parts[1]), Number(parts[2]));
        }
	      throw new Error("Malformed string date: " + stringDate);
    }
    throw new Error("Expected a date in string form but got " + JSON.stringify(stringDate));
}

function dateGetYear(date) {
    var d = mustBeDate(date);
	  return { "$nat" : d.year };
}

function dateGetMonth(date) {
    var d = mustBeDate(date);
	  return { "$nat" : d.month };
}

function dateGetDay(date) {
    var d = mustBeDate(date);
	  return { "$nat" : d.day };
}

function dateNe(date1, date2) {
    var d1 = mustBeDate(date1);
    var d2 = mustBeDate(date2);
    return compareDates(d1, d2) != 0;
}

function dateLt(date1, date2) {
    var d1 = mustBeDate(date1);
    var d2 = mustBeDate(date2);
    return compareDates(d1, d2) < 0;
}

function dateLe(date1, date2) {
    var d1 = mustBeDate(date1);
    var d2 = mustBeDate(date2);
    return compareDates(d1, d2) <= 0;
}

function dateGt(date1, date2) {
    var d1 = mustBeDate(date1);
    var d2 = mustBeDate(date2);
    return compareDates(d1, d2) > 0;
}

function dateGe(date1, date2) {
    var d1 = mustBeDate(date1);
    var d2 = mustBeDate(date2);
    return compareDates(d1, d2) >= 0;
}


function dateSetYear(date, year) {
    var d = mustBeDate(date);
    return boxDate(year, d.month, d.day);
}

function dateSetMonth(date, month) {
    var d = mustBeDate(date);
    /* Use Javascript Date object to normalize out-of-range month */
    var jsDate = new Date(d.year, month-1, d.day);
    return boxDate(jsDate.getFullYear(), jsDate.getMonth()+1, jsDate.getDate());
}

function dateSetDay(date, day) {
    var d = mustBeDate(date);
    /* Use Javascript Date object to normalize out-of-range day */
    var jsDate = new Date(d.year, d.month-1, day);
    return boxDate(jsDate.getFullYear(), jsDate.getMonth()+1, jsDate.getDate());
}

/* Period */
function periodFromString(stringPeriod) {
    // TODO verify what the string format for periods is going to be.
    // Here we assume a number adjoined to a valid unit with a dash.
    if (typeof stringPeriod === "string") {
	      parts = stringPeriod.split("-");
	      if (parts.length === 2) {
	          mustBeUnit(parts[1]);
	          return {"period": Number(parts[0]), "unit": parts[1]};
	          throw new Error("Malformed string period: " + stringPeriod);
	      }
	      throw new Error("Expected a period in string form but got " + JSON.stringify(stringPeriod));
    }
}

function periodPlus(date, period) {
    var d = mustBeDate(date);
    var i = mustBePeriod(period);
    switch(i.unit) {
    case DAY:
	      return dateSetDay(d, d.day + i.period);
    case MONTH:
	      return dateSetMonth(d, d.month + i.period);
    case YEAR:
	      return dateSetYear(d, d.year + i.period);
    default:
	      throw new Error("Unexpected state (not supposed to happen)");
    }
}

function periodMinus(date, period) {
    var d = mustBeDate(date);
    var i = mustBePeriod(period);
    switch(i.unit) {
    case DAY:
	      return dateNewDay(d, d.day - i.period);
    case MONTH:
	      return dateNewMonth(d, d.month - i.period);
    case YEAR:
	      return dateNewYear(de, d.year - i.period);
    default:
	      throw new Error("Unexpected bad unit (not supposed to happen)");
    }
}

function periodBetween(date1, date) {
    throw new Error("We don't know how to do 'period between' dates yet");
}
