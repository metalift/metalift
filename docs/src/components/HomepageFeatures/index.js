import React from 'react';
import clsx from 'clsx';
import styles from './styles.module.css';

const FeatureList = [
  {
    title: 'Easy to Use',
    Svg: require('@site/static/img/undraw_complete_design_re_h75h.svg').default,
    description: (
      <>
        Metalift offers a friendly Python API that makes it easy to analyze LLVM sources,
        define a target language for synthesis, and encode verification conditions.
      </>
    ),
  },
  {
    title: 'Powerful Algorithms Built In',
    Svg: require('@site/static/img/undraw_powerful_re_frhr.svg').default,
    description: (
      <>
        Metalift builds on the modern Rosette synthesis engine and the CVC5 theorem prover, making
        synthesis more efficient and enabling applications in complex domains.
      </>
    ),
  },
  {
    title: 'Designed for Flexibility',
    Svg: require('@site/static/img/undraw_building_blocks_re_5ahy.svg').default,
    description: (
      <>
        A variety of APIs make it easy to adapt Metalift for any task. Metalift has been applied in projects ranging from translating
        imperative Java to Spark, to synthesizing distributed system logic.
      </>
    ),
  },
];

function Feature({Svg, title, description}) {
  return (
    <div className={clsx('col col--4')}>
      <div className="text--center">
        <Svg className={styles.featureSvg} role="img" />
      </div>
      <div className="text--center padding-horiz--md">
        <h3>{title}</h3>
        <p>{description}</p>
      </div>
    </div>
  );
}

export default function HomepageFeatures() {
  return (
    <section className={styles.features}>
      <div className="container">
        <div className="row">
          {FeatureList.map((props, idx) => (
            <Feature key={idx} {...props} />
          ))}
        </div>
      </div>
    </section>
  );
}
