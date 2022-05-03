import React from 'react';
import clsx from 'clsx';
import Layout from '@theme/Layout';
import Link from '@docusaurus/Link';
import useDocusaurusContext from '@docusaurus/useDocusaurusContext';
import useBaseUrl from '@docusaurus/useBaseUrl';
import styles from './index.module.css';
import HomepageFeatures from '@site/src/components/HomepageFeatures';
import MetaliftSvg from './metalift-full.svg';

function HomepageHeader() {
  const {siteConfig} = useDocusaurusContext();
  const wideLogoUrl = useBaseUrl("img/metalift-full.svg");

  return (
    <header className={clsx('hero hero--primary', styles.heroBanner)}>
      <div className="container">
        <MetaliftSvg style={{ width: "100%" }}/>
        {/* <h1 style={{
          color: "white"
        }} className="hero__title">{siteConfig.title}</h1> */}
        <p style={{
          color: "white"
        }} className="hero__subtitle">{siteConfig.tagline}</p>
        <div className={styles.buttons}>
          <Link
            className="button button--secondary button--lg"
            to="/docs/installation">
            Get Started - 10 min ⏱️
          </Link>
        </div>
      </div>
    </header>
  );
}

export default function Home() {
  const {siteConfig} = useDocusaurusContext();
  return (
    <Layout
      description={siteConfig.tagline}>
      <HomepageHeader />
      <main>
        <HomepageFeatures />
      </main>
    </Layout>
  );
}
