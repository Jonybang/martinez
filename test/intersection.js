// import load from "load-json-file";

const martinez = require('../index');
const assert = require('assert');
const fs = require('fs');


const shapes = JSON.parse(fs.readFileSync(`${__dirname}/fixtures/hourglasses.geojson`).toString());

describe('intersect features', () => {
    it('returns polygons intersection', () => {
        // const shapes   = load.sync(path.join(__dirname, 'fixtures', 'hourglasses.geojson'));
        const subject = shapes.features[0];
        const clipping = shapes.features[1];
        // console.log('subject', subject.geometry.coordinates);
        //subject [ [ [ 0, 0 ], [ 0, 1 ], [ 1, 0 ], [ 1, 1 ], [ 0, 0 ] ] ]

        const result = martinez.intersection(subject.geometry.coordinates, clipping.geometry.coordinates);
        assert.deepEqual(result, [
            [
                // [
                    [0, 0.5],
                    [0.25, 0.75],
                    [0, 1],
                    [0, 0.5]
                // ]
            ],
            [
                // [
                    [0.75, 0.75],
                    [1, 0.5],
                    [1, 1],
                    [0.75, 0.75]
                // ]
            ]
        ]);
    });
});


describe('intersect case 1', () => {
    it('returns polygons intersection', () => {
        const basePolygon = [
            [
                [1.230889102444052694, 104.508869033306837081],
                [1.201198389753699301, 104.507961440831422805],
                [1.200340250506997107, 104.532680679112672805],
                [1.209607785567641256, 104.532165359705686569], //---
                [1.2108092475682497, 104.518947433680295944],
                [1.221278244629502294, 104.517917465418577194], //---
                [1.221964722499251363, 104.533367324620485305],
                [1.2300309631973505, 104.534265864640474318],
                // [1.230889102444052694, 104.508869033306837081]
            ]
        ];

        const cropPolygon = [
            [
                [1.194818755611777304, 104.524910990148782728],
                [1.195333572104573248, 104.542420450598001478],
                [1.23137441463768482, 104.540703836828470228],
                [1.232232553884387014, 104.523194376379251478], // |
                // [1.194818755611777304, 104.524910990148782728]
            ]
        ];

        const resultEvents = martinez.getResultEvents(basePolygon, cropPolygon);
        console.log('resultEvents.length', resultEvents.length);
        console.log('resultEvents', resultEvents.map(event => event.point));

        const result = martinez.intersection(basePolygon, cropPolygon);

        // console.log('result', result[1]);
        assert.deepEqual(result, [
            [
                // [
                    [1.200340250506997, 104.53268067911267],
                    [1.200619217705587, 104.52464485429624],
                    [1.2103318790951096, 104.52419921955585],
                    [1.2096077855676413, 104.53216535970569],
                    [1.200340250506997, 104.53268067911267]
                // ]
            ], [
                // [
                    [1.2215345212102309, 104.52368522176366],
                    [1.2304022226206794, 104.52327835533876],
                    [1.2300309631973505, 104.53426586464047],
                    [1.2219647224992514, 104.53336732462049],
                    [1.2215345212102309, 104.52368522176366]
                // ]
            ]
        ]);
    });
});

describe('intersect case 2', () => {
    it('returns polygons intersection', () => {
        const basePolygon = [
            [
                [1.2154430989176035, 104.49491517618299],
                [1.2149281147867441, 104.51156632974744],
                [1.2056605797261, 104.51156632974744],
                [1.2044591177254915, 104.51946275308728],
                [1.1963928770273924, 104.51946275308728],
                [1.1957063991576433, 104.49680345132947]
            ]
        ];

        const cropPolygon = [
            [
                [1.2065324652940035, 104.5116032101214],
                [1.1951483320444822, 104.51125787571073],
                [1.1958123464137316, 104.52563183382154],
                [1.206624498590827, 104.52494518831372]
            ]
        ];

        const result = martinez.intersection(basePolygon, cropPolygon);

        // console.log('result', JSON.stringify(result));
        assert.deepEqual(result, [
            [
                // [
                    [1.1961452212313757, 104.51128811605773],
                    [1.2056589997653093, 104.51157671379559],
                    [1.2044591177254915, 104.51946275308728],
                    [1.1963928770273924, 104.51946275308728],
                    [1.1961452212313757, 104.51128811605773]
                // ]
            ]
        ]);
    });
});

describe('intersect case 3', () => {
    it('returns polygons intersection', () => {
        const basePolygon = [
            [
                [1.2303741183131933, 104.50938368216157],
                [1.2290011625736952, 104.53134862706065],
                [1.2077200133353472, 104.53096406534314],
                [1.2051455955952406, 104.50950605794787],
                [1.2303741183131933, 104.50938368216157]
            ]
        ];

        const cropPolygon = [
            [
                [1.2221363838762045, 104.51723115518689],
                [1.2334633525460958, 104.51808946207166],
                [1.2392984982579947, 104.53714387491345],
                [1.2224795389920473, 104.54624192789197],
                [1.218360671773553, 104.520492721349],
                [1.2221363838762045, 104.51723115518689]
            ]
        ];

        const result = martinez.intersection(basePolygon, cropPolygon);

        // console.log('result', JSON.stringify(result));
        assert.deepEqual(result, [
            [
                // [
                    [1.218360671773553, 104.520492721349],
                    [1.2221363838762045, 104.51723115518689],
                    [1.229847077330825, 104.5178154369547],
                    [1.2290011625736952, 104.53134862706065],
                    [1.2200713803836252, 104.53118726113358],
                    [1.218360671773553, 104.520492721349]
                // ]
            ]
        ]);
    });
});

describe('intersect case 4', () => {
    it('returns polygons intersection', () => {
        const basePolygon = [
            [
                [1.2291728239506483, 104.51007032766938],
                [1.2037726398557425, 104.50989866629243],
                [1.2036009784787893, 104.53199403360486],
                [1.227113390341401, 104.53336732462049],
                [1.2291728239506483, 104.51007032766938]
            ]
        ];

        const cropPolygon = [
            [
                [1.2314039189368486, 104.52323930338025],
                [1.2152714375406504, 104.52255265787244],
                [1.2126970198005438, 104.54298002645373],
                [1.2344931531697512, 104.54898850992322],
                [1.2314039189368486, 104.52323930338025]
            ]
        ];

        const result = martinez.intersection(basePolygon, cropPolygon);

        // console.log('result', JSON.stringify(result));
        assert.deepEqual(result, [
            [
                // [
                    [1.2140049780825173, 104.53260170070706],
                    [1.2152714375406504, 104.52255265787244],
                    [1.2280214250378665, 104.52309533456454],
                    [1.227113390341401, 104.53336732462049],
                    [1.2140049780825173, 104.53260170070706]
                // ]
            ]
        ]);
    });
});


describe('intersect case 5', () => {
    it('returns polygons intersection', () => {
        const basePolygon = [
            [
                [1.2310605961829424, 104.49840137735009],
                [1.2307174410670996, 104.53272124752402],
                [1.2161295767873526, 104.53319566324353],
                [1.2163010705262423, 104.49714677408338],
                [1.2310605961829424, 104.49840137735009]
            ]
        ];

        const cropPolygon = [
            [
                [1.239641821011901, 104.50881941244006],
                [1.239641821011901, 104.51980607584119],
                [1.2046307791024446, 104.52135069295764],
                [1.2053172569721937, 104.50744612142444],
                [1.239641821011901, 104.50881941244006]
            ]
        ];

        const result = martinez.intersection(basePolygon, cropPolygon);

        // console.log('result', JSON.stringify(result));
        assert.deepEqual(result, [
            [
                [
                    [1.2161883520348686,104.52084079596509],
                    [1.2162499930504436,104.50788352911343],
                    [1.2309599021694357,104.50847205766722],
                    [1.2308426948764055,104.52019427568037],
                    [1.2161883520348686,104.52084079596509]
                ]
            ]
        ]);
    });
});
