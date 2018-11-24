const Tree = require('splaytree/dist/splay');
const Queue = require('tinyqueue');

const NORMAL = 0;
const NON_CONTRIBUTING = 1;
const SAME_TRANSITION = 2;
const DIFFERENT_TRANSITION = 3;

const INTERSECTION = 0;
const UNION = 1;
const DIFFERENCE = 2;
const XOR = 3;

const max = Math.max;
const min = Math.min;

let contourId = 0;
const EMPTY = [];

class SweepEvent {
    /**
     * Sweepline event
     *
     * @class {SweepEvent}
     * @param {Array.<Number>}  point
     * @param {Boolean}         left
     * @param {SweepEvent=}     otherEvent
     * @param {Boolean}         isSubject
     * @param {Number}          edgeType
     */
    constructor(point, left, otherEvent, isSubject, edgeType) {
        /**
         * Is left endpoint?
         * @type {Boolean}
         */
        this.left = left;
        /**
         * @type {Array.<Number>}
         */
        this.point = point;
        /**
         * Other edge reference
         * @type {SweepEvent}
         */
        this.otherEvent = otherEvent;
        /**
         * Belongs to source or clipping polygon
         * @type {Boolean}
         */
        this.isSubject = isSubject;
        /**
         * Edge contribution type
         * @type {Number}
         */
        this.type = edgeType || NORMAL;
        /**
         * In-out transition for the sweepline crossing polygon
         * @type {Boolean}
         */
        this.inOut = false;
        /**
         * @type {Boolean}
         */
        this.otherInOut = false;
        /**
         * Previous event in result?
         * @type {SweepEvent}
         */
        this.prevInResult = null;
        /**
         * Does event belong to result?
         * @type {Boolean}
         */
        this.inResult = false;
        // connection step
        /**
         * @type {Boolean}
         */
        this.resultInOut = false;

        this.isExteriorRing = true;
    }
    /**
     * @param  {Array.<Number>}  p
     * @return {Boolean}
     */
    isBelow(p) {
        const p0 = this.point, p1 = this.otherEvent.point;
        return this.left
            ? (p0[0] - p[0]) * (p1[1] - p[1]) - (p1[0] - p[0]) * (p0[1] - p[1]) > 0
            : (p1[0] - p[0]) * (p0[1] - p[1]) - (p0[0] - p[0]) * (p1[1] - p[1]) > 0;
    }
    /**
     * @param  {Array.<Number>}  p
     * @return {Boolean}
     */
    isAbove(p) {
        return !this.isBelow(p);
    }
    /**
     * @return {Boolean}
     */
    isVertical() {
        return this.point[0] === this.otherEvent.point[0];
    }
    clone() {
        const copy = new SweepEvent(
            this.point, this.left, this.otherEvent, this.isSubject, this.type);

        copy.inResult = this.inResult;
        copy.prevInResult = this.prevInResult;
        copy.isExteriorRing = this.isExteriorRing;
        copy.inOut = this.inOut;
        copy.otherInOut = this.otherInOut;

        return copy;
    }
}

/**
 * Finds the magnitude of the cross product of two vectors (if we pretend
 * they're in three dimensions)
 *
 * @param {Object} a First vector
 * @param {Object} b Second vector
 * @private
 * @returns {Number} The magnitude of the cross product
 */
function crossProduct(a, b) {
    return (a[0] * b[1]) - (a[1] * b[0]);
}

/**
 * Finds the dot product of two vectors.
 *
 * @param {Object} a First vector
 * @param {Object} b Second vector
 * @private
 * @returns {Number} The dot product
 */
function dotProduct(a, b) {
    return (a[0] * b[0]) + (a[1] * b[1]);
}
function subdivideSegments(eventQueue, subject, clipping, sbbox, cbbox, operation) {
    const sweepLine = new Tree(compareSegments);
    const sortedEvents = [];

    const rightbound = Math.min(sbbox[2], cbbox[2]);

    let prev, next, begin;

    while (eventQueue.length !== 0) {
        let event = eventQueue.pop();
        sortedEvents.push(event);
        // optimization by bboxes for intersection and difference goes here
        if ((operation === INTERSECTION && event.point[0] > rightbound) ||
            (operation === DIFFERENCE   && event.point[0] > sbbox[2])) {
            break;
        }
        if (event.left) {
            next  = prev = sweepLine.insert(event);
            begin = sweepLine.minNode();

            if (prev !== begin) prev = sweepLine.prev(prev);
            else                prev = null;

            next = sweepLine.next(next);

            const prevEvent = prev ? prev.key : null;
            let prevprevEvent;
            computeFields(event, prevEvent, operation);
            if (next) {
                if (possibleIntersection(event, next.key, eventQueue) === 2) {
                    computeFields(event, prevEvent, operation);
                    computeFields(event, next.key, operation);
                }
            }

            if (prev) {
                if (possibleIntersection(prev.key, event, eventQueue) === 2) {
                    let prevprev = prev;
                    if (prevprev !== begin) prevprev = sweepLine.prev(prevprev);
                    else                    prevprev = null;

                    prevprevEvent = prevprev ? prevprev.key : null;
                    computeFields(prevEvent, prevprevEvent, operation);
                    computeFields(event,     prevEvent,     operation);
                }
            }
        } else {
            event = event.otherEvent;
            next = prev = sweepLine.find(event);

            if (prev && next) {

                if (prev !== begin) prev = sweepLine.prev(prev);
                else                prev = null;

                next = sweepLine.next(next);
                sweepLine.remove(event);

                if (next && prev) {
                    possibleIntersection(prev.key, next.key, eventQueue);
                }
            }
        }
    }
    return sortedEvents;
}

/**
 * Finds the intersection (if any) between two line segments a and b, given the
 * line segments' end points a1, a2 and b1, b2.
 *
 * This algorithm is based on Schneider and Eberly.
 * http://www.cimec.org.ar/~ncalvo/Schneider_Eberly.pdf
 * Page 244.
 *
 * @param {Array.<Number>} a1 point of first line
 * @param {Array.<Number>} a2 point of first line
 * @param {Array.<Number>} b1 point of second line
 * @param {Array.<Number>} b2 point of second line
 * @param {Boolean=}       noEndpointTouch whether to skip single touchpoints
 *                                         (meaning connected segments) as
 *                                         intersections
 * @returns {Array.<Array.<Number>>|Null} If the lines intersect, the point of
 * intersection. If they overlap, the two end points of the overlapping segment.
 * Otherwise, null.
 */
function segemntIntersection(a1, a2, b1, b2, noEndpointTouch) {
    // The algorithm expects our lines in the form P + sd, where P is a point,
    // s is on the interval [0, 1], and d is a vector.
    // We are passed two points. P can be the first point of each pair. The
    // vector, then, could be thought of as the distance (in x and y components)
    // from the first point to the second point.
    // So first, let's make our vectors:
    const va = [a2[0] - a1[0], a2[1] - a1[1]];
    const vb = [b2[0] - b1[0], b2[1] - b1[1]];
    // We also define a function to convert back to regular point form:

    /* eslint-disable arrow-body-style */

    function toPoint(p, s, d) {
        return [
            p[0] + s * d[0],
            p[1] + s * d[1]
        ];
    }

    /* eslint-enable arrow-body-style */

    // The rest is pretty much a straight port of the algorithm.
    const e = [b1[0] - a1[0], b1[1] - a1[1]];
    let kross = crossProduct(va, vb);
    let sqrKross = kross * kross;
    const sqrLenA = dotProduct(va, va);
    //const sqrLenB  = dotProduct(vb, vb);

    // Check for line intersection. This works because of the properties of the
    // cross product -- specifically, two vectors are parallel if and only if the
    // cross product is the 0 vector. The full calculation involves relative error
    // to account for possible very small line segments. See Schneider & Eberly
    // for details.
    if (sqrKross > 0/* EPS * sqrLenB * sqLenA */) {
        // If they're not parallel, then (because these are line segments) they
        // still might not actually intersect. This code checks that the
        // intersection point of the lines is actually on both line segments.
        const s = crossProduct(e, vb) / kross;
        if (s < 0 || s > 1) {
            // not on line segment a
            return null;
        }
        const t = crossProduct(e, va) / kross;
        if (t < 0 || t > 1) {
            // not on line segment b
            return null;
        }
        if (s === 0 || s === 1) {
            // on an endpoint of line segment a
            return noEndpointTouch ? null : [toPoint(a1, s, va)];
        }
        if (t === 0 || t === 1) {
            // on an endpoint of line segment b
            return noEndpointTouch ? null : [toPoint(b1, t, vb)];
        }
        return [toPoint(a1, s, va)];
    }

    // If we've reached this point, then the lines are either parallel or the
    // same, but the segments could overlap partially or fully, or not at all.
    // So we need to find the overlap, if any. To do that, we can use e, which is
    // the (vector) difference between the two initial points. If this is parallel
    // with the line itself, then the two lines are the same line, and there will
    // be overlap.
    //const sqrLenE = dotProduct(e, e);
    kross = crossProduct(e, va);
    sqrKross = kross * kross;

    if (sqrKross > 0 /* EPS * sqLenB * sqLenE */) {
        // Lines are just parallel, not the same. No overlap.
        return null;
    }

    const sa = dotProduct(va, e) / sqrLenA;
    const sb = sa + dotProduct(va, vb) / sqrLenA;
    const smin = Math.min(sa, sb);
    const smax = Math.max(sa, sb);

    // this is, essentially, the FindIntersection acting on floats from
    // Schneider & Eberly, just inlined into this function.
    if (smin <= 1 && smax >= 0) {

        // overlap on an end point
        if (smin === 1) {
            return noEndpointTouch ? null : [toPoint(a1, smin > 0 ? smin : 0, va)];
        }

        if (smax === 0) {
            return noEndpointTouch ? null : [toPoint(a1, smax < 1 ? smax : 1, va)];
        }

        if (noEndpointTouch && smin === 0 && smax === 1) return null;

        // There's overlap on a segment -- two points of intersection. Return both.
        return [
            toPoint(a1, smin > 0 ? smin : 0, va),
            toPoint(a1, smax < 1 ? smax : 1, va)
        ];
    }

    return null;
}

function trivialOperation(subject, clipping, operation) {
    let result = null;
    if (subject.length * clipping.length === 0) {
        if (operation === INTERSECTION) {
            result = EMPTY;
        } else if (operation === DIFFERENCE) {
            result = subject;
        } else if (operation === UNION ||
            operation === XOR) {
            result = (subject.length === 0) ? clipping : subject;
        }
    }
    return result;
}


function compareBBoxes(subject, clipping, sbbox, cbbox, operation) {
    let result = null;
    if (sbbox[0] > cbbox[2] ||
        cbbox[0] > sbbox[2] ||
        sbbox[1] > cbbox[3] ||
        cbbox[1] > sbbox[3]) {
        if (operation === INTERSECTION) {
            result = EMPTY;
        } else if (operation === DIFFERENCE) {
            result = subject;
        } else if (operation === UNION ||
            operation === XOR) {
            result = subject.concat(clipping);
        }
    }
    return result;
}

function processPolygon(contourOrHole, isSubject, depth, eventQueue, bbox, isExteriorRing) {
    let i, len, s1, s2, e1, e2;
    for (i = 0, len = contourOrHole.length - 1; i < len; i++) {
        s1 = contourOrHole[i];
        s2 = contourOrHole[i + 1];
        e1 = new SweepEvent(s1, false, undefined, isSubject);
        e2 = new SweepEvent(s2, false, e1, isSubject);
        e1.otherEvent = e2;

        if (s1[0] === s2[0] && s1[1] === s2[1]) {
            continue; // skip collapsed edges, or it breaks
        }

        e1.contourId = e2.contourId = depth;
        if (!isExteriorRing) {
            e1.isExteriorRing = false;
            e2.isExteriorRing = false;
        }
        if (compareEvents(e1, e2) > 0) {
            e2.left = true;
        } else {
            e1.left = true;
        }

        const x = s1[0], y = s1[1];
        bbox[0] = min(bbox[0], x);
        bbox[1] = min(bbox[1], y);
        bbox[2] = max(bbox[2], x);
        bbox[3] = max(bbox[3], y);

        // Pushing it so the queue is sorted from left to right,
        // with object on the left having the highest priority.
        eventQueue.push(e1);
        eventQueue.push(e2);
    }
}


function fillQueue(subject, clipping, sbbox, cbbox, operation) {
    const eventQueue = new Queue(null, compareEvents);
    let polygonSet, isExteriorRing, i, ii, j, jj; //, k, kk;

    for (i = 0, ii = subject.length; i < ii; i++) {
        polygonSet = subject[i];
        for (j = 0, jj = polygonSet.length; j < jj; j++) {
            isExteriorRing = j === 0;
            if (isExteriorRing) contourId++;
            processPolygon(polygonSet[j], true, contourId, eventQueue, sbbox, isExteriorRing);
        }
    }

    for (i = 0, ii = clipping.length; i < ii; i++) {
        polygonSet = clipping[i];
        for (j = 0, jj = polygonSet.length; j < jj; j++) {
            isExteriorRing = j === 0;
            if (operation === DIFFERENCE) isExteriorRing = false;
            if (isExteriorRing) contourId++;
            processPolygon(polygonSet[j], false, contourId, eventQueue, cbbox, isExteriorRing);
        }
    }

    return eventQueue;
}

/**
 * Signed area of the triangle (p0, p1, p2)
 * @param  {Array.<Number>} p0
 * @param  {Array.<Number>} p1
 * @param  {Array.<Number>} p2
 * @return {Number}
 */
function signedArea(p0, p1, p2) {
    return (p0[0] - p2[0]) * (p1[1] - p2[1]) - (p1[0] - p2[0]) * (p0[1] - p2[1]);
}

/**
 * @param  {SweepEvent} e1
 * @param  {SweepEvent} e2
 * @return {Number}
 */
function compareEvents(e1, e2) {
    const p1 = e1.point;
    const p2 = e2.point;

    // Different x-coordinate
    if (p1[0] > p2[0])
        return 1;
    if (p1[0] < p2[0])
        return -1;

    // Different points, but same x-coordinate
    // Event with lower y-coordinate is processed first
    if (p1[1] !== p2[1])
        return p1[1] > p2[1] ? 1 : -1;

    return specialCases(e1, e2, p1, p2);
}

/**
 * @param  {SweepEvent} le1
 * @param  {SweepEvent} le2
 * @return {Number}
 */
function compareSegments(le1, le2) {
    if (le1 === le2) return 0;

    // Segments are not collinear
    if (signedArea(le1.point, le1.otherEvent.point, le2.point) !== 0 ||
        signedArea(le1.point, le1.otherEvent.point, le2.otherEvent.point) !== 0) {

        // If they share their left endpoint use the right endpoint to sort
        if (equals(le1.point, le2.point))
            return le1.isBelow(le2.otherEvent.point) ? -1 : 1;
        // Different left endpoint: use the left endpoint to sort
        if (le1.point[0] === le2.point[0])
            return le1.point[1] < le2.point[1] ? -1 : 1;
        // has the line segment associated to e1 been inserted
        // into S after the line segment associated to e2 ?
        if (compareEvents(le1, le2) === 1)
            return le2.isAbove(le1.point) ? -1 : 1;
        // The line segment associated to e2 has been inserted
        // into S after the line segment associated to e1
        return le1.isBelow(le2.point) ? -1 : 1;
    }

    if (le1.isSubject === le2.isSubject) { // same polygon
        let p1 = le1.point, p2 = le2.point;
        if (p1[0] === p2[0] && p1[1] === p2[1]/*equals(le1.point, le2.point)*/) {
            p1 = le1.otherEvent.point;
            p2 = le2.otherEvent.point;
            if (p1[0] === p2[0] && p1[1] === p2[1]) return 0;
            else return le1.contourId > le2.contourId ? 1 : -1;
        }
    } else { // Segments are collinear, but belong to separate polygons
        return le1.isSubject ? -1 : 1;
    }

    return compareEvents(le1, le2) === 1 ? 1 : -1;
}

/* eslint-disable no-unused-vars */
function specialCases(e1, e2, p1, p2) {
    // Same coordinates, but one is a left endpoint and the other is
    // a right endpoint. The right endpoint is processed first
    if (e1.left !== e2.left)
        return e1.left ? 1 : -1;

    // const p2 = e1.otherEvent.point, p3 = e2.otherEvent.point;
    // const sa = (p1[0] - p3[0]) * (p2[1] - p3[1]) - (p2[0] - p3[0]) * (p1[1] - p3[1])
    // Same coordinates, both events
    // are left endpoints or right endpoints.
    // not collinear
    if (signedArea(p1, e1.otherEvent.point, e2.otherEvent.point) !== 0) {
        // the event associate to the bottom segment is processed first
        return (!e1.isBelow(e2.otherEvent.point)) ? 1 : -1;
    }

    return (!e1.isSubject && e2.isSubject) ? 1 : -1;
}

/* eslint-enable no-unused-vars */
/**
 * @param  {SweepEvent} event
 * @param  {SweepEvent} prev
 * @param  {Operation} operation
 */
function computeFields(event, prev, operation) {
    // compute inOut and otherInOut fields
    if (prev === null) {
        event.inOut = false;
        event.otherInOut = true;

        // previous line segment in sweepline belongs to the same polygon
    } else {
        if (event.isSubject === prev.isSubject) {
            event.inOut = !prev.inOut;
            event.otherInOut = prev.otherInOut;

            // previous line segment in sweepline belongs to the clipping polygon
        } else {
            event.inOut = !prev.otherInOut;
            event.otherInOut = prev.isVertical() ? !prev.inOut : prev.inOut;
        }

        // compute prevInResult field
        if (prev) {
            event.prevInResult = (!inResult(prev, operation) || prev.isVertical())
                ? prev.prevInResult : prev;
        }
    }

    // check if the line segment belongs to the Boolean operation
    event.inResult = inResult(event, operation);
}


/* eslint-disable indent */
function inResult(event, operation) {
    switch (event.type) {
        case NORMAL:
            switch (operation) {
                case INTERSECTION:
                    return !event.otherInOut;
                case UNION:
                    return event.otherInOut;
                case DIFFERENCE:
                    // return (event.isSubject && !event.otherInOut) ||
                    //         (!event.isSubject && event.otherInOut);
                    return (event.isSubject && event.otherInOut) ||
                        (!event.isSubject && !event.otherInOut);
                case XOR:
                    return true;
            }
            break;
        case SAME_TRANSITION:
            return operation === INTERSECTION || operation === UNION;
        case DIFFERENT_TRANSITION:
            return operation === DIFFERENCE;
        case NON_CONTRIBUTING:
            return false;
    }
    return false;
}

/* eslint-enable indent */
/**
 * @param  {Array.<SweepEvent>} sortedEvents
 * @return {Array.<SweepEvent>}
 */
function orderEvents(sortedEvents) {
    let event, i, len, tmp;
    const resultEvents = [];
    for (i = 0, len = sortedEvents.length; i < len; i++) {
        event = sortedEvents[i];
        if ((event.left && event.inResult) ||
            (!event.left && event.otherEvent.inResult)) {
            resultEvents.push(event);
        }
    }
    // Due to overlapping edges the resultEvents array can be not wholly sorted
    let sorted = false;
    while (!sorted) {
        sorted = true;
        for (i = 0, len = resultEvents.length; i < len; i++) {
            if ((i + 1) < len &&
                compareEvents(resultEvents[i], resultEvents[i + 1]) === 1) {
                tmp = resultEvents[i];
                resultEvents[i] = resultEvents[i + 1];
                resultEvents[i + 1] = tmp;
                sorted = false;
            }
        }
    }
    for (i = 0, len = resultEvents.length; i < len; i++) {
        event = resultEvents[i];
        event.pos = i;
    }

    // imagine, the right event is found in the beginning of the queue,
    // when his left counterpart is not marked yet
    for (i = 0, len = resultEvents.length; i < len; i++) {
        event = resultEvents[i];
        if (!event.left) {
            tmp = event.pos;
            event.pos = event.otherEvent.pos;
            event.otherEvent.pos = tmp;
        }
    }

    return resultEvents;
}


/**
 * @param  {Number} pos
 * @param  {Array.<SweepEvent>} resultEvents
 * @param  {Object>}    processed
 * @return {Number}
 */
function nextPos(pos, resultEvents, processed, origIndex) {
    let p, p1;
    let newPos = pos + 1;
    const length = resultEvents.length;

    p = resultEvents[pos].point;

    if (newPos < length)
        p1 = resultEvents[newPos].point;

    // while in range and not the current one by value
    while (newPos < length && p1[0] === p[0] && p1[1] === p[1]) {
        if (!processed[newPos]) {
            return newPos;
        } else {
            newPos++;
        }
        p1 = resultEvents[newPos].point;
    }

    newPos = pos - 1;

    while (processed[newPos] && newPos >= origIndex) {
        newPos--;
    }
    return newPos;
}


/**
 * @param  {Array.<SweepEvent>} sortedEvents
 * @return {Array.<*>} polygons
 */
function connectEdges(sortedEvents, operation) {
    let i, len;
    const resultEvents = orderEvents(sortedEvents);

    // "false"-filled array
    const processed = {};
    const result = [];
    let event;

    for (i = 0, len = resultEvents.length; i < len; i++) {
        if (processed[i]) continue;
        const contour = [[]];

        if (!resultEvents[i].isExteriorRing) {
            if (operation === DIFFERENCE && !resultEvents[i].isSubject && result.length === 0) {
                result.push(contour);
            } else if (result.length === 0) {
                result.push([[contour]]);
            } else {
                result[result.length - 1].push(contour[0]);
            }
        } else if (operation === DIFFERENCE && !resultEvents[i].isSubject && result.length > 1) {
            result[result.length - 1].push(contour[0]);
        } else {
            result.push(contour);
        }

        const ringId = result.length - 1;
        let pos = i;

        const initial = resultEvents[i].point;
        contour[0].push(initial);

        while (pos >= i) {
            event = resultEvents[pos];
            processed[pos] = true;

            if (event.left) {
                event.resultInOut = false;
                event.contourId = ringId;
            } else {
                event.otherEvent.resultInOut = true;
                event.otherEvent.contourId = ringId;
            }

            pos = event.pos;
            processed[pos] = true;
            contour[0].push(resultEvents[pos].point);
            pos = nextPos(pos, resultEvents, processed, i);
        }

        pos = pos === -1 ? i : pos;

        event = resultEvents[pos];
        processed[pos] = processed[event.pos] = true;
        event.otherEvent.resultInOut = true;
        event.otherEvent.contourId = ringId;
    }

    // Handle if the result is a polygon (eg not multipoly)
    // Commented it again, let's see what do we mean by that
    // if (result.length === 1) result = result[0];
    return result;
}

/**
 * @param  {SweepEvent} se
 * @param  {Array.<Number>} p
 * @param  {Queue} eventQueue
 * @return {Queue}
 */
function divideSegment(se, p, eventQueue) {
    const r = new SweepEvent(p, false, se, se.isSubject);
    const l = new SweepEvent(p, true, se.otherEvent, se.isSubject);

    /* eslint-disable no-console */
    if (equals(se.point, se.otherEvent.point)) {

        console.warn('what is that, a collapsed segment?', se);
    }
    /* eslint-enable no-console */

    r.contourId = l.contourId = se.contourId;

    // avoid a rounding error. The left event would be processed after the right event
    if (compareEvents(l, se.otherEvent) > 0) {
        se.otherEvent.left = true;
        l.left = false;
    }

    // avoid a rounding error. The left event would be processed after the right event
    // if (compareEvents(se, r) > 0) {}

    se.otherEvent.otherEvent = l;
    se.otherEvent = r;

    eventQueue.push(l);
    eventQueue.push(r);

    return eventQueue;
}

function possibleIntersection(se1, se2, eventQueue) {
    // that disallows self-intersecting polygons,
    // did cost us half a day, so I'll leave it
    // out of respect
    // if (se1.isSubject === se2.isSubject) return;
    const inter = segemntIntersection(
        se1.point, se1.otherEvent.point,
        se2.point, se2.otherEvent.point
    );

    const nintersections = inter ? inter.length : 0;
    if (nintersections === 0) return 0; // no intersection

    // the line segments intersect at an endpoint of both line segments
    if ((nintersections === 1) &&
        (equals(se1.point, se2.point) ||
            equals(se1.otherEvent.point, se2.otherEvent.point))) {
        return 0;
    }

    if (nintersections === 2 && se1.isSubject === se2.isSubject) {
        return 0;
    }

    // The line segments associated to se1 and se2 intersect
    if (nintersections === 1) {
        // if the intersection point is not an endpoint of se1
        if (!equals(se1.point, inter[0]) && !equals(se1.otherEvent.point, inter[0])) {
            divideSegment(se1, inter[0], eventQueue);
        }
        // if the intersection point is not an endpoint of se2
        if (!equals(se2.point, inter[0]) && !equals(se2.otherEvent.point, inter[0])) {
            divideSegment(se2, inter[0], eventQueue);
        }
        return 1;
    }

    // The line segments associated to se1 and se2 overlap
    const events = [];
    let leftCoincide = false;
    let rightCoincide = false;

    if (equals(se1.point, se2.point)) {
        leftCoincide = true; // linked
    } else if (compareEvents(se1, se2) === 1) {
        events.push(se2, se1);
    } else {
        events.push(se1, se2);
    }

    if (equals(se1.otherEvent.point, se2.otherEvent.point)) {
        rightCoincide = true;
    } else if (compareEvents(se1.otherEvent, se2.otherEvent) === 1) {
        events.push(se2.otherEvent, se1.otherEvent);
    } else {
        events.push(se1.otherEvent, se2.otherEvent);
    }

    if ((leftCoincide && rightCoincide) || leftCoincide) {
        // both line segments are equal or share the left endpoint
        se2.type = NON_CONTRIBUTING;
        se1.type = (se2.inOut === se1.inOut)
            ? SAME_TRANSITION : DIFFERENT_TRANSITION;

        if (leftCoincide && !rightCoincide) {
            // honestly no idea, but changing events selection from [2, 1]
            // to [0, 1] fixes the overlapping self-intersecting polygons issue
            divideSegment(events[1].otherEvent, events[0].point, eventQueue);
        }
        return 2;
    }

    // the line segments share the right endpoint
    if (rightCoincide) {
        divideSegment(events[0], events[1].point, eventQueue);
        return 3;
    }

    // no line segment includes totally the other one
    if (events[0] !== events[3].otherEvent) {
        divideSegment(events[0], events[1].point, eventQueue);
        divideSegment(events[1], events[2].point, eventQueue);
        return 3;
    }

    // one line segment includes the other one
    divideSegment(events[0], events[1].point, eventQueue);
    divideSegment(events[3].otherEvent, events[2].point, eventQueue);

    return 3;
}

function equals(p1, p2) {
    if (p1[0] === p2[0]) {
        if (p1[1] === p2[1]) {
            return true;
        } else {
            return false;
        }
    }
    return false;
}

function boolean(subject, clipping, operation) {
    if (typeof subject[0][0][0] === 'number') {
        subject = [subject];
    }
    if (typeof clipping[0][0][0] === 'number') {
        clipping = [clipping];
    }
    let trivial = trivialOperation(subject, clipping, operation);
    if (trivial) {
        return trivial === EMPTY ? null : trivial;
    }
    const sbbox = [Infinity, Infinity, -Infinity, -Infinity];
    const cbbox = [Infinity, Infinity, -Infinity, -Infinity];

    //console.time('fill queue');
    const eventQueue = fillQueue(subject, clipping, sbbox, cbbox, operation);
    //console.timeEnd('fill queue');

    trivial = compareBBoxes(subject, clipping, sbbox, cbbox, operation);
    if (trivial) {
        return trivial === EMPTY ? null : trivial;
    }
    //console.time('subdivide edges');
    const sortedEvents = subdivideSegments(eventQueue, subject, clipping, sbbox, cbbox, operation);
    //console.timeEnd('subdivide edges');

    //console.time('connect vertices');
    const result = connectEdges(sortedEvents, operation);
    //console.timeEnd('connect vertices');
    return result;
}

function union(subject, clipping) {
    return boolean(subject, clipping, UNION);
}

function diff(subject, clipping) {
    return boolean(subject, clipping, DIFFERENCE);
}

function xor(subject, clipping) {
    return boolean(subject, clipping, XOR);
}

function intersection(subject, clipping) {
    return boolean(subject, clipping, INTERSECTION);
}

module.exports = {
    intersection
};
