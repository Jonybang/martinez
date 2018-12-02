module.exports = function LinkedList(comparator) {
    const nodesByIds = {};
    const valuesByIds = {};
    let headId = null;
    let count = 0;

    this.find = (value) => {
        return binarySearch(value);
    };

    this.insert = this.push = (value) => {
        if (!headId) {
            headId = ++count;
            nodesByIds[headId] = {
                nextId: null,
                prevId: null
            };
            valuesByIds[headId] = value;
            return headId;
        }
        const foundLeft = binarySearch(value, true);
        // console.log('foundLeft', foundLeft);

        const compareResult = comparator(valuesByIds[foundLeft], value);

        if (compareResult === 0) {
            return foundLeft;
        } else if (compareResult < 0) {
            // console.log('insertAfter', foundLeft);
            return this.insertAfter(foundLeft, value);
        } else {
            if (foundLeft === headId) {
                const newId = ++count;
                nodesByIds[newId] = {
                    nextId: headId,
                    prevId: null
                };
                valuesByIds[newId] = value;

                nodesByIds[headId].prevId = newId;
                // console.log('insert head', newId, nodesByIds);
                headId = newId;
                return newId;
            }
            // console.log('headId', headId, nodesByIds[headId]);
            // console.log('foundLeft', foundLeft, nodesByIds[foundLeft]);

            // console.log('insertBefore', foundLeft);
            return this.insertAfter(nodesByIds[foundLeft].prevId, value);
        }
    };

    this.insertAfter = function(prevId, value) {
        const newId = ++count;
        valuesByIds[newId] = value;

        nodesByIds[newId] = {
            nextId: nodesByIds[prevId].nextId,
            prevId: prevId
        };

        // console.log('insertAfter', newId, nodesByIds[newId]);

        nodesByIds[prevId].nextId = newId;
        if (nodesByIds[newId].nextId) {
            nodesByIds[nodesByIds[newId].nextId].prevId = newId;
        }
        return newId;
    };

    this.remove = function(id) {
        if (!id) {
            return;
        }
        const node = nodesByIds[id];
        // console.log('before remove', id, nodesByIds);

        if (node.prevId) {
            nodesByIds[node.prevId].nextId = node.nextId;
        }
        if (node.nextId) {
            nodesByIds[node.nextId].prevId = node.prevId;
        }

        if (id === headId) {
            headId = node.nextId;
        }

        delete nodesByIds[id];

        // console.log('after remove', id, nodesByIds);
    };

    this.swap = function (aId, bId) {
        const aNode = nodesByIds[aId];
        const bNode = nodesByIds[bId];
        const aNodePrevId = aNode.prevId;
        const aNodeNextId = aNode.nextId;
        const bNodePrevId = bNode.prevId;
        const bNodeNextId = bNode.nextId;

        // console.log('before swap', aId, bId, nodesByIds);

        if (aNodePrevId === bId) {
            aNode.prevId = aId;
            bNode.nextId = bId;
        } else if (aNodeNextId === bId) {
            aNode.nextId = aId;
            bNode.prevId = bId;
        }

        if (aNodePrevId) {
            nodesByIds[aNodePrevId].nextId = bId;
        }
        if (aNodeNextId) {
            nodesByIds[aNodeNextId].prevId = bId;
        }
        if (bNodePrevId) {
            nodesByIds[bNodePrevId].nextId = aId;
        }
        if (bNodeNextId) {
            nodesByIds[bNodeNextId].prevId = aId;
        }


        //a: { prevId: 3, nextId: b }
        //b: { prevId: a, nextId: null }

        nodesByIds[aId] = bNode;
        nodesByIds[bId] = aNode;

        if (!nodesByIds[aId].prevId) {
            headId = aId;
        }
        if (!nodesByIds[bId].prevId) {
            headId = bId;
        }

        // console.log('after swap', aId, bId, nodesByIds);
    };

    this.getIndex = function (id) {
        if (!id) {
            return null;
        }
        let curId = headId;
        let index = 0;
        do {
            if (curId === id) {
                return index;
            }
            curId = nodesByIds[curId].nextId;
            index++;
        } while (true);
    };

    this.min = function (aId, bId) {
        const compareResult = comparator(valuesByIds[aId], valuesByIds[bId]);
        if (compareResult < 0) {
            return aId;
        } else {
            return bId;
        }
    };

    this.max = function (aId, bId) {
        const compareResult = comparator(valuesByIds[aId], valuesByIds[bId]);
        if (compareResult > 0) {
            return aId;
        } else {
            return bId;
        }
    };

    this.next = function(id, mul) {
        if (!id || !nodesByIds[id].nextId) {
            return null;
        }
        if (mul === 1 || !mul) {
            return nodesByIds[id].nextId;
        } else {
            return this.next(nodesByIds[id].nextId, mul - 1);
        }
    };

    this.prev = function(id, mul) {
        console.log('prev', id, nodesByIds);
        if (!id || !nodesByIds[id].prevId) {
            return null;
        }
        if (mul === 1 || !mul) {
            return nodesByIds[id].prevId;
        } else {
            return this.next(nodesByIds[id].prevId, mul - 1);
        }
    };

    this.getValue = function(id) {
        return valuesByIds[id];
    };

    this.pop = function() {
        const popId = headId;
        const lastNode = nodesByIds[popId];
        if (lastNode.nextId) {
            nodesByIds[lastNode.nextId].prevId = null;
            headId = lastNode.nextId;
        }

        delete nodesByIds[popId];

        console.log('LogPop', 'popId', popId, 'headId', headId, 'count', count);
        
        return valuesByIds[popId];
    };
    
    this.isEmpty = function () {
        return !headId;
    };

    function binarySearch(value, returnLeft = false) {
        // console.log('binarySearch begin', returnLeft, headId, nodesByIds);
        if (!headId) {
            return null;
        }

        let curId = headId;
        // let prevId = null;

        do {
            let compareResult = comparator(valuesByIds[curId], value);
            // if (valuesByIds[curId].point[0] === 1.2108092475682497 && value.point[0] === 1.2108092475682497) {
                console.log('CompareResult1', 'point:', JSON.stringify(valuesByIds[curId].point))//, 'left:', valuesByIds[curId].left, 'isSubject:', valuesByIds[curId].isSubject);
                console.log('CompareResult2', 'point:', JSON.stringify(value.point))//, 'left:', value.left, 'isSubject:', value.isSubject);
                console.log('CompareResult3', compareResult);
            // }

            if (compareResult === 0) {
                return curId;
            } else if (!returnLeft) {
                if (!nodesByIds[curId].nextId) {
                    return null;
                }
                curId = nodesByIds[curId].nextId;
            } else {
                if (compareResult < 0 && nodesByIds[curId].nextId) {
                    curId = nodesByIds[curId].nextId;
                } else {
                    return curId;
                }
            }
        } while (true);
    }
};
